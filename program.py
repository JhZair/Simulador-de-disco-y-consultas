"""06/29/2026 4:16pm
Simulación de Almacenamiento Físico de Base de Datos
CustomTkinter · Windows 11 · Python 3.12

Modelo: SLOTTED PAGES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Cada sector es una "página" compartida. Varios registros
(o fragmentos de registros) pueden convivir en la misma
página. No hay padding desperdiciado al final de un registro
porque el espacio libre queda disponible para el siguiente.

Formato de página (sector):
┌──────────────────────────────────────────────────────┐
│ PAGE HEADER  (fijo, PAGE_HDR bytes)                  │
│   next_page : int32  página siguiente encadenada (-1)│
│   free_ptr  : int16  offset del inicio del espacio   │
│                      libre (crece →)                 │
│   slot_count: int16  número de slots usados          │
├──────────────────────────────────────────────────────┤
│ SLOT DIRECTORY  (crece desde el final ←)             │
│   slot[n-1]: (offset int16, length int16)  4 bytes   │
│   slot[n-2]: ...                                     │
│   ...                                                │
├──────────────────────────────────────────────────────┤
│ ESPACIO LIBRE  (entre datos y slot directory)        │
├──────────────────────────────────────────────────────┤
│ DATOS  (crecen desde el inicio →)                    │
│   fragmento del registro en slot[0]                  │
│   fragmento del registro en slot[1]                  │
│   ...                                                │
└──────────────────────────────────────────────────────┘

El AVL indexa por PK → lista de (page_id, slot_idx).
Un registro grande se fragmenta en varios slots
(posiblemente en varias páginas), todos encadenados.
"""

import csv
import io
import json
import re
import struct
import tkinter as tk
from tkinter import filedialog, messagebox
from dataclasses import dataclass, asdict, field
from typing import Any, Optional

import customtkinter as ctk

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")


# ══════════════════════════════════════════════════════════════════════════════
#  COLORES  (constantes — sin concatenaciones en runtime)
# ══════════════════════════════════════════════════════════════════════════════

BG        = "#0b1120"
PANEL     = "#111c2e"
DARK      = "#0a1520"
BORDER    = "#1e3048"
ACCENT    = "#00c8f8"
ACCENT_D  = "#0a2535"
ACCENT_H  = "#0f3a50"
ACCENT2   = "#a855f7"
ACCENT2_D = "#1e1030"
ACCENT2_B = "#3d2270"
GREEN     = "#10d98a"
GREEN_D   = "#0c2e1e"
GREEN_H   = "#0f3d28"
YELLOW    = "#fbbf24"
YELLOW_D  = "#332510"
YELLOW_H  = "#4a3518"
RED       = "#f87171"
RED_D     = "#2d0f0f"
RED_H     = "#3d1515"
ORANGE    = "#fb923c"
MUTED     = "#4a6480"
MUTED_D   = "#111c2e"
TEXT      = "#dce8f5"

PLATTER   = ["#0ea5e9", "#a855f7", "#f59e0b", "#10b981"]
PLATTER_D = ["#075272", "#521a7a", "#7a5200", "#0a6640"]

FM  = ("Consolas", 11)
FMS = ("Consolas", 10)
FT  = ("Consolas", 10, "bold")
FL  = ("Consolas",  9)


# ══════════════════════════════════════════════════════════════════════════════
#  CONSTANTES DE PÁGINA
# ══════════════════════════════════════════════════════════════════════════════

# PAGE HEADER: next_page(int32) + free_ptr(int16) + slot_count(int16)
PAGE_HDR_FMT  = ">iHH"        # 4 + 2 + 2 = 8 bytes
PAGE_HDR_SIZE = struct.calcsize(PAGE_HDR_FMT)   # 8

# SLOT ENTRY: offset(int16) + length(int16)
SLOT_FMT  = ">HH"
SLOT_SIZE = struct.calcsize(SLOT_FMT)   # 4

# Marcador de página vacía / sin encadenamiento
NO_PAGE = -1


# ══════════════════════════════════════════════════════════════════════════════
#  GEOMETRÍA DEL DISCO
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class DiskConfig:
    platters:           int
    tracks_per_surface: int
    sectors_per_track:  int
    sector_size_bytes:  int

    @property
    def surfaces(self):
        return self.platters * 2

    @property
    def total_sectors(self):
        return self.surfaces * self.tracks_per_surface * self.sectors_per_track

    @property
    def total_bytes(self):
        return self.total_sectors * self.sector_size_bytes

    @property
    def usable_bytes(self):
        """Bytes disponibles para datos + slot directory en cada página."""
        return self.sector_size_bytes - PAGE_HDR_SIZE


# ══════════════════════════════════════════════════════════════════════════════
#  DIRECCIÓN FÍSICA
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class DiskAddress:
    platter: int
    surface: int
    track:   int
    sector:  int

    def __str__(self):
        return (f"Plato {self.platter} | Sup {self.surface} | "
                f"Pista {self.track:03d} | Sector {self.sector:03d}")

    def to_dict(self):
        return asdict(self)


# ══════════════════════════════════════════════════════════════════════════════
#  SLOTTED PAGE
# ══════════════════════════════════════════════════════════════════════════════

class SlottedPage:
    """
    Página (sector) con slot directory.

    Memoria interna  →  bytearray de sector_size_bytes:
      [PAGE_HDR | datos→ ... espacio libre ... ←slot_dir]

    free_ptr  apunta al primer byte libre tras los datos.
    El slot directory crece desde el final hacia el inicio.
    Hay espacio libre mientras:
        free_ptr + slot_size_nueva_entrada <= sector_size - slot_count*SLOT_SIZE
    """

    def __init__(self, page_size: int):
        self.page_size  = page_size
        self.data       = bytearray(page_size)
        self.next_page  = NO_PAGE
        self.free_ptr   = PAGE_HDR_SIZE   # justo tras el header
        self.slots:     list[tuple[int,int]] = []   # (offset, length)

    # ── espacio disponible ────────────────────────────────────────────────────

    @property
    def free_space(self) -> int:
        """Bytes libres reales (espacio para datos + un slot nuevo)."""
        slot_dir_start = self.page_size - len(self.slots) * SLOT_SIZE
        return max(0, slot_dir_start - self.free_ptr - SLOT_SIZE)

    @property
    def occupancy_pct(self) -> float:
        # datos escritos + espacio que ocupa el slot directory
        used = (self.free_ptr - PAGE_HDR_SIZE) + len(self.slots) * SLOT_SIZE
        cap  = self.page_size - PAGE_HDR_SIZE
        return round(min(used / cap * 100, 100.0), 1) if cap > 0 else 0.0

    @property
    def slot_count(self) -> int:
        return len(self.slots)

    # ── insertar fragmento ────────────────────────────────────────────────────

    def insert(self, fragment: bytes) -> Optional[int]:
        """
        Inserta `fragment` en la página si hay espacio.
        Retorna el slot_idx asignado, o None si no cabe.
        """
        if len(fragment) > self.free_space:
            return None
        offset = self.free_ptr
        self.data[offset:offset + len(fragment)] = fragment
        self.free_ptr += len(fragment)
        self.slots.append((offset, len(fragment)))
        return len(self.slots) - 1

    # ── eliminar fragmento (para rollback) ───────────────────────────────────

    def delete(self, slot_idx: int) -> bool:
        """
        Libera el slot `slot_idx` para rollback de escrituras parciales.

        Si es el último slot (caso típico de rollback atómico), retrocede
        free_ptr y elimina el slot → recupera espacio real.
        Si está en medio, lo marca con length=0 (espacio no recuperable
        sin compactación — análogo a un DELETE en página fragmentada).

        Retorna True si se liberó espacio real, False si solo se marcó.
        """
        if slot_idx >= len(self.slots):
            return False
        offset, length = self.slots[slot_idx]
        if slot_idx == len(self.slots) - 1:
            # Último slot: retroceder el puntero y eliminar el slot
            self.free_ptr = offset
            self.slots.pop()
            self.data[offset:offset + length] = bytes(length)
            return True
        else:
            # Slot en medio: marcar como eliminado (length=0)
            self.slots[slot_idx] = (offset, 0)
            return False

    # ── leer fragmento ────────────────────────────────────────────────────────

    def read(self, slot_idx: int) -> bytes:
        if slot_idx >= len(self.slots):
            return b""
        offset, length = self.slots[slot_idx]
        return bytes(self.data[offset:offset + length])

    # ── serialización (para mostrar en popup) ────────────────────────────────

    def to_bytes(self) -> bytes:
        hdr = struct.pack(PAGE_HDR_FMT,
                          self.next_page, self.free_ptr, len(self.slots))
        out = bytearray(self.page_size)
        out[:PAGE_HDR_SIZE] = hdr
        # datos
        out[PAGE_HDR_SIZE:self.free_ptr] = \
            self.data[PAGE_HDR_SIZE:self.free_ptr]
        # slot directory (al final)
        for i, (off, ln) in enumerate(self.slots):
            pos = self.page_size - (i + 1) * SLOT_SIZE
            out[pos:pos + SLOT_SIZE] = struct.pack(SLOT_FMT, off, ln)
        return bytes(out)


# ══════════════════════════════════════════════════════════════════════════════
#  DISCO SIMULADO
# ══════════════════════════════════════════════════════════════════════════════

class Disk:
    """
    Disco con slotted pages.

    write_record(data) → list[(page_id, slot_idx)]
        Intenta llenar la página actual antes de abrir una nueva.
        Si un fragmento no cabe en la página actual, abre una nueva
        y encadena via next_page.
        Retorna la lista de (page_id, slot_idx) de cada fragmento.

    read_record(fragments) → bytes
        Dado [(page_id, slot_idx), ...] reconstruye el registro completo.
    """

    def __init__(self, config: DiskConfig):
        self.config       = config
        self._pages:      dict[int, SlottedPage] = {}
        self._current_pid = 0          # página abierta actualmente
        self._next_pid    = 0          # próximo page_id a asignar
        self._allocate_page()          # crear primera página

    # ── gestión de páginas ────────────────────────────────────────────────────

    def _allocate_page(self) -> int:
        if self._next_pid >= self.config.total_sectors:
            raise OverflowError("Disco lleno")
        pid = self._next_pid
        self._pages[pid] = SlottedPage(self.config.sector_size_bytes)
        self._next_pid += 1
        return pid

    def _current_page(self) -> SlottedPage:
        return self._pages[self._current_pid]

    # ── conversiones lineal ↔ dirección ──────────────────────────────────────

    def linear_to_address(self, pid: int) -> DiskAddress:
        c   = self.config
        sec = pid % c.sectors_per_track
        tg  = pid // c.sectors_per_track
        t   = tg  % c.tracks_per_surface
        sg  = tg  // c.tracks_per_surface
        return DiskAddress(sg // 2, sg % 2, t, sec)

    def address_to_linear(self, a: DiskAddress) -> int:
        c  = self.config
        sg = a.platter * 2 + a.surface
        tg = sg * c.tracks_per_surface + a.track
        return tg * c.sectors_per_track + a.sector

    # ── escritura ─────────────────────────────────────────────────────────────

    def write_record(self, data: bytes) -> list[tuple[int, int]]:
        """
        Escribe `data` distribuyéndola en slots de páginas.
        Un registro grande se reparte en varios fragmentos.
        El espacio libre de una página se aprovecha al máximo
        antes de abrir una nueva → cero padding desperdiciado.

        ATOMICIDAD (comportamiento SGBD profesional):
          Si el disco se llena a mitad de escritura, se hace rollback
          de todos los fragmentos parciales ya escritos antes de lanzar
          OverflowError. El disco queda en el mismo estado que antes
          de llamar a write_record — igual que un ROLLBACK en un SGBD.

        Retorna lista de (page_id, slot_idx) para cada fragmento.
        Lanza OverflowError("Disco lleno") si no hay espacio suficiente.
        """
        fragments: list[tuple[int, int]] = []
        # Snapshot del estado del disco para rollback si falla
        pid_snapshot      = self._current_pid
        next_pid_snapshot = self._next_pid
        pos = 0

        try:
            while pos < len(data):
                page = self._current_page()

                # ¿cabe algo en la página actual?
                avail = page.free_space
                if avail <= 0:
                    # abrir nueva página y encadenar
                    new_pid = self._allocate_page()   # puede lanzar OverflowError
                    page.next_page = new_pid
                    self._current_pid = new_pid
                    page = self._current_page()
                    avail = page.free_space

                chunk    = data[pos:pos + avail]
                slot_idx = page.insert(chunk)
                if slot_idx is None:
                    raise RuntimeError(
                        f"Error interno: página {self._current_pid} reportó "
                        f"{avail}B libres pero insert() falló. "
                        f"Posible corrupción de página."
                    )

                fragments.append((self._current_pid, slot_idx))
                pos += len(chunk)

        except OverflowError:
            # ── ROLLBACK ─────────────────────────────────────────────────────
            # Eliminar fragmentos parciales ya escritos en páginas existentes
            for frag_pid, frag_slot in fragments:
                page = self._pages.get(frag_pid)
                if page is not None:
                    page.delete(frag_slot)
            # Desalojar páginas nuevas creadas durante este write (si las hubo)
            for pid_to_remove in range(next_pid_snapshot, self._next_pid):
                self._pages.pop(pid_to_remove, None)
            # Restaurar punteros de estado
            self._current_pid = pid_snapshot
            self._next_pid    = next_pid_snapshot
            # Quitar next_page del encadenamiento si se había parcheado
            if pid_snapshot in self._pages:
                self._pages[pid_snapshot].next_page = None
            raise   # re-lanzar OverflowError al llamador

        return fragments

    # ── lectura ───────────────────────────────────────────────────────────────

    def read_record(self, fragments: list[tuple[int, int]]) -> bytes:
        """Reconstruye el registro leyendo cada (page_id, slot_idx)."""
        return b"".join(
            page.read(slot_idx)
            for pid, slot_idx in fragments
            if (page := self._pages.get(pid))
        )

    def get_page(self, pid: int) -> Optional[SlottedPage]:
        return self._pages.get(pid)

    def pages_used(self) -> int:
        return self._next_pid

    def flush(self):
        """No-op: todo está en RAM, no hay archivo que sincronizar."""
        pass

    def close(self):
        """No-op: no hay archivo abierto que cerrar."""
        pass


# ══════════════════════════════════════════════════════════════════════════════
#  AVL TREE  (índice por PK)
# ══════════════════════════════════════════════════════════════════════════════

class AVLNode:
    """
    Nodo genérico del AVL.
    values almacena:
      - En el árbol PRIMARIO (PK):     [(page_id, slot_idx), ...]
      - En los árboles SECUNDARIOS:    [pk1, pk2, ...]  (lista de PKs)
    """
    __slots__ = ("key", "values", "left", "right", "height")

    def __init__(self, key, value):
        self.key    = key
        self.values = [value]
        self.left   = None
        self.right  = None
        self.height = 1


class DuplicateKeyError(Exception):
    """
    Lanzada por AVL(unique=True) cuando se intenta insertar
    una clave que ya existe en el índice.
    Equivalente a la violación de restricción PRIMARY KEY / UNIQUE
    en un SGBD profesional (PostgreSQL: 'duplicate key value
    violates unique constraint').
    """


class AVL:
    """
    AVL Tree genérico auto-balanceado.
    Soporta claves comparables (int, float, str).

    unique=True  → índice primario / UNIQUE:
                   cada clave mapea exactamente a UN valor.
                   Insertar una clave duplicada lanza DuplicateKeyError.
                   Comportamiento idéntico al B-Tree primario de PostgreSQL/MySQL.

    unique=False → índice secundario (no-único):
                   cada clave acumula una lista de valores (PKs).
                   Múltiples filas pueden compartir el mismo valor de columna.

    insert(key, value)        O(log n)
    search(key)               O(log n) → list[value] | []
    range_search(lo, hi)      O(log n + k) → list[(key, values)]
    """

    def __init__(self, unique: bool = False):
        self.root:   Optional[AVLNode] = None
        self.size:   int  = 0
        self.unique: bool = unique

    def _h(self, n) -> int:
        return n.height if n else 0

    def _bf(self, n) -> int:
        return self._h(n.left) - self._h(n.right)

    def _upd(self, n):
        n.height = 1 + max(self._h(n.left), self._h(n.right))

    def _rot_right(self, y):
        x = y.left; y.left = x.right; x.right = y
        self._upd(y); self._upd(x); return x

    def _rot_left(self, x):
        y = x.right; x.right = y.left; y.left = x
        self._upd(x); self._upd(y); return y

    def _balance(self, n):
        self._upd(n)
        bf = self._bf(n)
        if bf > 1:
            if self._bf(n.left) < 0:
                n.left = self._rot_left(n.left)
            return self._rot_right(n)
        if bf < -1:
            if self._bf(n.right) > 0:
                n.right = self._rot_right(n.right)
            return self._rot_left(n)
        return n

    def _insert(self, node, key, value) -> tuple:
        """
        Retorna (node, created).
        - unique=True  : clave duplicada → lanza DuplicateKeyError (no modifica el árbol)
        - unique=False : clave duplicada → acumula value en la lista del nodo existente
        """
        if node is None:
            return AVLNode(key, value), True
        if key == node.key:
            if self.unique:
                # Violación de restricción PRIMARY KEY / UNIQUE
                raise DuplicateKeyError(
                    f"ERROR: violación de restricción de unicidad — "
                    f"la clave duplicada '{key}' viola la restricción PRIMARY KEY"
                )
            # Índice secundario: acumular PKs distintas
            if value not in node.values:
                node.values.append(value)
            return node, False
        if key < node.key:
            node.left,  created = self._insert(node.left,  key, value)
        else:
            node.right, created = self._insert(node.right, key, value)
        return self._balance(node), created

    def insert(self, key, value):
        self.root, created = self._insert(self.root, key, value)
        if created:
            self.size += 1   # solo cuenta nodos físicos del árbol

    def search(self, key) -> list:
        cur = self.root
        while cur:
            if key == cur.key: return cur.values
            cur = cur.left if key < cur.key else cur.right
        return []

    def _range(self, n, lo, hi, out):
        if n is None: return
        if lo < n.key:  self._range(n.left,  lo, hi, out)
        if lo <= n.key <= hi: out.append((n.key, n.values))
        if n.key < hi:  self._range(n.right, lo, hi, out)

    def range_search(self, lo, hi) -> list[tuple]:
        out = []; self._range(self.root, lo, hi, out); return out

    def bfs(self) -> list[list[dict]]:
        if not self.root: return []
        levels = []; queue = [(self.root, 0, None, "")]
        while queue:
            next_q = []; level = []
            for node, nid, pid, side in queue:
                level.append({"key": node.key, "bf": self._bf(node),
                              "h": node.height, "id": nid,
                              "pid": pid, "side": side})
                if node.left:  next_q.append((node.left,  nid*2+1, nid, "L"))
                if node.right: next_q.append((node.right, nid*2+2, nid, "R"))
            levels.append(level); queue = next_q
        return levels


# ══════════════════════════════════════════════════════════════════════════════
#  ESQUEMA SQL
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class ColumnDef:
    name:     str
    sql_type: str
    is_pk:    bool = False
    not_null: bool = False
    py_type:  type = str

    def cast(self, v: Any) -> Any:
        """
        Castea `v` al tipo de la columna de forma tolerante.
        - Valores vacíos/None → 0, 0.0 o "" según el tipo (no crashea)
        - "10.0" en columna INT → 10  (via float intermedio)
        - Texto en columna INT → 0   (valor seguro por defecto)
        - Tipos desconocidos  → str(v)
        """
        # Valor vacío → default seguro según tipo
        if v is None or (isinstance(v, str) and v.strip() == ""):
            if self.py_type is int:   return 0
            if self.py_type is float: return 0.0
            return ""

        if self.py_type is int:
            try:
                return int(float(v))   # maneja "10.0", "10", 10.0
            except (ValueError, TypeError):
                return 0               # texto en columna INT → 0

        if self.py_type is float:
            try:
                return float(v)
            except (ValueError, TypeError):
                return 0.0

        # str y cualquier otro tipo
        return str(v).strip()


@dataclass
class TableSchema:
    name:    str
    columns: list

    @property
    def pk_column(self) -> Optional[str]:
        for c in self.columns:
            if c.is_pk: return c.name
        return self.columns[0].name if self.columns else None

    def cast_row(self, row: dict) -> dict:
        cm = {c.name: c for c in self.columns}
        return {k: cm[k].cast(v) if k in cm else v for k, v in row.items()}


# ── Tipos SQL → Python  (cobertura exhaustiva multi-dialecto) ─────────────────
#
# MySQL / MariaDB / PostgreSQL / SQLite / SQL Server / Oracle / DB2
# Regla: si el tipo almacena números enteros → int
#         si almacena números reales          → float
#         cualquier otra cosa                 → str  (seguro para comparar y mostrar)

_INT_TYPES: set[str] = {
    # SQL estándar
    "INT", "INTEGER", "SMALLINT", "BIGINT", "TINYINT",
    # MySQL / MariaDB
    "MEDIUMINT", "INT1", "INT2", "INT3", "INT4", "INT8",
    "UNSIGNED", "SIGNED",
    # PostgreSQL
    "INT2", "INT4", "INT8", "SERIAL", "SMALLSERIAL", "BIGSERIAL",
    "OID", "XID", "CID",
    # SQL Server
    "BIT",                          # 0/1 → int
    # SQLite
    "ROWID",
    # Oracle
    "NUMBER",                       # sin decimales → int (ver _sql_to_py)
    # DB2
    "DECFLOAT",                     # entero cuando precision=0
    # Alias comunes
    "BOOL", "BOOLEAN",              # internamente 0/1
    "YEAR",                         # MySQL YEAR → entero de 4 dígitos
    "COUNTER",                      # Access
}

_FLOAT_TYPES: set[str] = {
    # SQL estándar
    "FLOAT", "REAL", "DOUBLE", "NUMERIC", "DECIMAL", "DEC",
    # MySQL
    "DOUBLE PRECISION", "FIXED",
    # PostgreSQL
    "FLOAT4", "FLOAT8", "MONEY",
    # SQL Server
    "SMALLMONEY",
    # Oracle
    "BINARY_FLOAT", "BINARY_DOUBLE",
    # IBM DB2
    "DECFLOAT",
    # Alias
    "NUMBER",                       # Oracle NUMBER con decimales → float
    "CURRENCY",                     # Access
}

# Todo lo demás → str. No hace falta listarlo: cualquier tipo no reconocido
# cae en el fallback str, que es seguro para UUID, JSONB, ARRAY, INET, etc.

def _sql_to_py(raw_type: str) -> type:
    """
    Convierte tipo SQL a tipo Python. Cobertura exhaustiva multi-dialecto.
    Tipos desconocidos → str (nunca crashea).

    Reglas especiales:
    - NUMBER(p,0) o NUMBER(p) sin escala → int  (Oracle)
    - NUMBER(p,s) con s>0               → float (Oracle)
    - DOUBLE PRECISION                  → float (PostgreSQL / SQL estándar)
    - UNSIGNED / SIGNED                 → int   (MySQL modificador de tipo)
    """
    raw   = raw_type.strip()
    upper = raw.upper()

    # DOUBLE PRECISION: dos palabras, caso especial
    if re.match(r"DOUBLE\s+PRECISION", upper):
        return float

    # Extraer base y parámetros: DECIMAL(10,2) → base="DECIMAL", params="10,2"
    m = re.match(r"([A-Z_ ]+?)(?:\(([^)]*)\))?$", upper.strip())
    base   = m.group(1).strip() if m else upper
    params = m.group(2)         if m else None

    # Oracle NUMBER: NUMBER(p,0) → int, NUMBER(p,s>0) → float
    if base in ("NUMBER",):
        if params:
            parts = [p.strip() for p in params.split(",")]
            if len(parts) == 2:
                try:
                    return int if int(parts[1]) == 0 else float
                except ValueError:
                    pass
            # NUMBER(p) sin escala → int
            return int
        # NUMBER sin parámetros → float (más seguro)
        return float

    if base in _INT_TYPES:   return int
    if base in _FLOAT_TYPES: return float
    return str   # fallback universal: UUID, JSONB, ARRAY, INET, XML, etc.


def parse_schema(text: str) -> TableSchema:
    """
    Parser CREATE TABLE de nivel profesional. Soporta:

    DIALECTOS:
      MySQL / MariaDB, PostgreSQL, SQLite, SQL Server (T-SQL),
      Oracle, IBM DB2, Access — en un único parser.

    SINTAXIS SOPORTADA:
      ✓ CREATE TABLE / CREATE TABLE IF NOT EXISTS
      ✓ CREATE TEMPORARY TABLE / CREATE TEMP TABLE
      ✓ Nombres con backticks `t`, comillas dobles "t", corchetes [t] (T-SQL),
        comillas simples 't', sin comillas
      ✓ Esquema calificado: schema.tabla, `db`.`tabla`, [dbo].[tabla]
      ✓ Tipos con precisión: VARCHAR(255), DECIMAL(10,2), NUMERIC(18,4)
      ✓ Tipos de dos palabras: DOUBLE PRECISION, CHARACTER VARYING,
        BINARY VARYING, NATIONAL CHAR, LONG RAW, etc.
      ✓ PRIMARY KEY inline y separado
      ✓ PKs compuestas: PRIMARY KEY (col_a, col_b) → usa col_a como PK
        y avisa sobre col_b
      ✓ CONSTRAINT nombre PRIMARY KEY (...)
      ✓ FOREIGN KEY, UNIQUE, CHECK, INDEX, KEY — ignorados silenciosamente
      ✓ NOT NULL, NULL, AUTO_INCREMENT, AUTOINCREMENT, IDENTITY(1,1),
        GENERATED ALWAYS AS IDENTITY, DEFAULT <valor>, DEFAULT (<expr>),
        UNIQUE inline, UNSIGNED, ZEROFILL, CHARACTER SET, COLLATE,
        ON UPDATE, COMMENT, REFERENCES, CHECK (<expr>)
      ✓ Comentarios -- y /* ... */ (incluso multilínea)
      ✓ Sin PK definida → primera columna como PK (fallback seguro)
      ✓ Columnas sin tipo → VARCHAR fallback

    RETORNA: TableSchema con pk_column = primera PK detectada (o col[0])
    LANZA:   ValueError solo si no hay columnas en absoluto
    """

    # ── 0. Normalizar saltos de línea ─────────────────────────────────────
    text = text.replace("\r\n", "\n").replace("\r", "\n")

    # ── 1. Eliminar comentarios ───────────────────────────────────────────
    # /* ... */ multilínea
    clean = re.sub(r'/\*.*?\*/', ' ', text, flags=re.DOTALL)
    # -- hasta fin de línea
    clean = re.sub(r'--[^\n]*', ' ', clean)
    # # hasta fin de línea (MySQL shell, algunos dumps)
    clean = re.sub(r'#[^\n]*',  ' ', clean)
    # Normalizar espacios
    clean = " ".join(clean.split())

    # ── 2. Extraer nombre de tabla ────────────────────────────────────────
    # Soporta: CREATE [TEMPORARY|TEMP] TABLE [IF NOT EXISTS]
    #   nombre simple, schema.tabla, db.schema.tabla
    #   con cualquier combinación de ` " [ ] ' o sin comillas
    _QI = r'(?:[`"\[]?)(\w+)(?:[`"\]]?)'   # identificador opcionalmente entre comillas
    # prefijo opcional: uno o dos niveles de schema (db.schema. o schema.)
    _PREFIX = rf'(?:{_QI}\.)*'             # cero o más niveles de prefijo

    tbl_pat = re.compile(
        r"CREATE\s+(?:TEMPORARY\s+|TEMP\s+)?TABLE\s+"
        r"(?:IF\s+NOT\s+EXISTS\s+)?"
        + _PREFIX + _QI + r"\s*\(",
        re.IGNORECASE
    )
    m = tbl_pat.search(clean)
    if not m:
        raise ValueError(
            "No se encontró CREATE TABLE válido.\n"
            "Formatos aceptados:\n"
            "  CREATE TABLE nombre (...)\n"
            "  CREATE TABLE IF NOT EXISTS nombre (...)\n"
            "  CREATE TEMPORARY TABLE nombre (...)\n"
            "  CREATE TABLE esquema.tabla (...)\n"
            "  CREATE TABLE db.esquema.tabla (...)\n"
            "  CREATE TABLE `nombre` (...)   -- backticks\n"
            "  CREATE TABLE [dbo].[nombre] (...) -- T-SQL"
        )
    # El último grupo capturado es el nombre de la tabla (sin schema)
    name = m.group(m.lastindex)

    # ── 3. Extraer cuerpo (contador de paréntesis, ignora strings) ────────
    start = clean.index("(", m.start()) + 1
    depth = 1
    i = start
    in_str = None   # ' o "
    while i < len(clean) and depth:
        c = clean[i]
        if in_str:
            if c == in_str:
                in_str = None
        elif c in ("'", '"'):
            in_str = c
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        i += 1
    body = clean[start:i - 1].strip()

    # ── 4. Split de cláusulas respetando paréntesis Y strings ────────────
    # Problema sin este fix: DEFAULT 'hola,mundo' se parte en la coma
    # Solución: rastrear si estamos dentro de '' o "" además de ()
    parts: list[str] = []
    depth    = 0
    in_str   = None   # None | "'" | '"'
    buf      = []
    i_body   = 0
    while i_body < len(body):
        ch = body[i_body]
        if in_str:
            buf.append(ch)
            if ch == in_str:
                # ¿escape de comilla duplicada? ('it''s' en SQL)
                if i_body + 1 < len(body) and body[i_body + 1] == in_str:
                    buf.append(body[i_body + 1])
                    i_body += 1
                else:
                    in_str = None
        elif ch in ("'", '"'):
            in_str = ch
            buf.append(ch)
        elif ch == "(":
            depth += 1; buf.append(ch)
        elif ch == ")":
            depth -= 1; buf.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(buf).strip()); buf = []
        else:
            buf.append(ch)
        i_body += 1
    if buf:
        parts.append("".join(buf).strip())

    # ── 5. Palabras clave de restricciones de tabla (no son columnas) ─────
    _TABLE_CONSTRAINTS = re.compile(
        r"^(?:PRIMARY\s+KEY|FOREIGN\s+KEY|UNIQUE\s+(?:KEY|INDEX)?|"
        r"UNIQUE$|CHECK\s*\(|CONSTRAINT\s+(?:\w|[`\"\[\'])|INDEX\s+|KEY\s+|"
        r"FULLTEXT|SPATIAL|CLUSTERED|NONCLUSTERED)",
        re.IGNORECASE
    )

    # ── 6. Modificadores inline a ignorar ─────────────────────────────────
    _INLINE_STRIP = re.compile(
        r"\b(?:"
        r"NOT\s+NULL|NULL|AUTO_INCREMENT|AUTOINCREMENT|"
        r"IDENTITY\s*\([^)]*\)|GENERATED\s+(?:ALWAYS|BY\s+DEFAULT)\s+AS\s+IDENTITY(?:\s*\([^)]*\))?|"
        r"GENERATED\s+ALWAYS\s+AS\s*\([^)]*\)\s*(?:STORED|VIRTUAL)?|"
        r"DEFAULT\s*(?:\([^)]*\)|\S+)|"
        r"UNIQUE(?:\s+KEY)?|UNSIGNED|SIGNED|ZEROFILL|"
        r"CHARACTER\s+SET\s+\w+|CHARSET\s+\w+|COLLATE\s+\w+|"
        r"ON\s+UPDATE\s+\S+|"
        r"COMMENT\s+'[^']*'|"
        r"REFERENCES\s+\S+(?:\s*\([^)]*\))?(?:\s+ON\s+(?:DELETE|UPDATE)\s+\w+(?:\s+\w+)?)*|"
        r"CHECK\s*\([^)]*\)|"
        r"ENABLE|DISABLE|NOCHECK|WITH\s+(?:CHECK|NOCHECK)|"
        r"SPARSE|ROWGUIDCOL|FILESTREAM|"
        r"VISIBLE|INVISIBLE|"                  # MySQL 8
        r"PRIMARY\s+KEY|"                      # inline PK — detectada antes de strip
        r")\b",
        re.IGNORECASE
    )

    # ── 7. Tipos de dos (o más) palabras ──────────────────────────────────
    _TWO_WORD_TYPES = re.compile(
        r"^(?:"
        r"DOUBLE\s+PRECISION|CHARACTER\s+VARYING|BINARY\s+VARYING|"
        r"NATIONAL\s+(?:CHAR(?:ACTER)?|VARCHAR)|"
        r"LONG\s+(?:RAW|VARCHAR|VARBINARY)|"
        r"TIMESTAMP\s+WITH(?:OUT)?\s+(?:LOCAL\s+)?TIME\s+ZONE|"
        r"INTERVAL\s+\w+(?:\s+TO\s+\w+)?|"
        r"BIT\s+VARYING|"
        r"FLOAT\s+UNSIGNED|INT\s+UNSIGNED|BIGINT\s+UNSIGNED|"
        r"SMALLINT\s+UNSIGNED|TINYINT\s+UNSIGNED|MEDIUMINT\s+UNSIGNED"
        r")(?:\s*\([^)]*\))?",
        re.IGNORECASE
    )

    cols:       list[ColumnDef] = []
    pk_columns: list[str]       = []
    pk_warnings: list[str]      = []

    for part in parts:
        part = part.strip()
        if not part:
            continue

        upper_part = part.upper().lstrip()

        # ── 7a. ¿Restricción de tabla? ────────────────────────────────────
        if _TABLE_CONSTRAINTS.match(upper_part):
            # Capturar PK compuesta: PRIMARY KEY (col_a, col_b, ...)
            pk_m = re.search(
                r"PRIMARY\s+KEY\s*\(([^)]+)\)", part, re.IGNORECASE)
            if pk_m:
                found_pks = [
                    k.strip().strip("`\"[]'")
                    for k in pk_m.group(1).split(",")
                ]
                pk_columns.extend(found_pks)
                if len(found_pks) > 1:
                    pk_warnings.append(
                        f"PK compuesta detectada {found_pks} — "
                        f"se usará '{found_pks[0]}' como clave primaria. "
                        f"Las demás columnas ({', '.join(found_pks[1:])}) "
                        f"se indexan normalmente."
                    )
            continue

        # ── 7b. Extraer nombre de columna ─────────────────────────────────
        # Soporta: `nombre`, "nombre", [nombre], 'nombre', nombre
        cname_m = re.match(
            r"^(?:`([^`]+)`|\"([^\"]+)\"|"
            r"\[([^\]]+)\]|'([^']+)'|(\w+))",
            part
        )
        if not cname_m:
            continue
        cname = next(g for g in cname_m.groups() if g is not None)
        rest  = part[cname_m.end():].strip()

        if not rest:
            # Columna sin tipo (SQLite lo permite) → VARCHAR, posible PK inline
            cols.append(ColumnDef(
                name=cname, sql_type="VARCHAR",
                py_type=str, is_pk=False, not_null=False
            ))
            continue

        # ── 7c. ¿PK inline? ───────────────────────────────────────────────
        is_pk = bool(re.search(r"\bPRIMARY\s+KEY\b", rest, re.IGNORECASE))
        if is_pk:
            pk_columns.append(cname)

        # ── 7d. Extraer tipo ──────────────────────────────────────────────
        # Quitar PRIMARY KEY del inicio de rest antes de extraer tipo
        rest_for_type = re.sub(r"^PRIMARY\s+KEY\s*", "", rest.strip(), flags=re.IGNORECASE).strip()
        if not rest_for_type:
            # Solo tenía PRIMARY KEY sin tipo → VARCHAR (SQLite)
            raw_type = "VARCHAR"
        else:
            # Primero intentar tipo de dos palabras
            two = _TWO_WORD_TYPES.match(rest_for_type)
            if two:
                raw_type = two.group(0).strip()
            else:
                # Tipo simple: primera palabra con paréntesis opcional
                type_m = re.match(
                    r"([`\w]+(?:\s*\([^)]*\))?)",
                    rest_for_type
                )
                raw_type = (type_m.group(1).strip().strip("`")
                            if type_m else "VARCHAR")

        # Limpiar modificadores del tipo (UNSIGNED, etc.) si quedaron pegados
        raw_type_clean = re.sub(
            r"\s+(?:UNSIGNED|SIGNED|ZEROFILL)$", "",
            raw_type, flags=re.IGNORECASE).strip()

        # ── 7e. ¿NOT NULL? ────────────────────────────────────────────────
        not_null = is_pk or bool(
            re.search(r"\bNOT\s+NULL\b", rest, re.IGNORECASE))

        cols.append(ColumnDef(
            name     = cname,
            sql_type = raw_type_clean,
            is_pk    = is_pk,
            not_null = not_null,
            py_type  = _sql_to_py(raw_type_clean),
        ))

    # ── 8. Marcar PKs detectadas en restricciones de tabla ────────────────
    pk_set = set(pk_columns)
    for c in cols:
        if c.name in pk_set:
            c.is_pk    = True
            c.not_null = True

    # ── 9. Fallback: sin PK → primera columna ────────────────────────────
    if not any(c.is_pk for c in cols) and cols:
        cols[0].is_pk    = True
        cols[0].not_null = True

    if not cols:
        raise ValueError(
            "No se encontraron columnas válidas en el CREATE TABLE.\n"
            "Verifica que el archivo sea un CREATE TABLE estándar SQL."
        )

    schema = TableSchema(name, cols)
    schema._pk_warnings = pk_warnings   # para mostrar en la UI si se desea
    return schema


# ══════════════════════════════════════════════════════════════════════════════
#  DATABASE MANAGER
# ══════════════════════════════════════════════════════════════════════════════

class DatabaseManager:
    """
    Orquesta Disk (slotted pages) + AVL por demanda + TableSchema.

    Los índices AVL NO se construyen al cargar los datos.
    Se construyen la primera vez que se busca por esa columna
    y se reutilizan mientras el programa esté abierto.
    Si se reinicia, se reconstruyen al buscar de nuevo.

    indices: dict[col_name → AVL]   (vacío al inicio, se llena por demanda)
    _records[pk] = {
        "record":    dict,
        "fragments": [(page_id, slot_idx), ...],
        "raw_len":   int,
    }
    """

    def __init__(self, disk: Disk):
        self.disk                    = disk
        self.indices: dict[str, AVL] = {}   # se llena solo al buscar
        self.schema: Optional[TableSchema] = None
        self.records_loaded          = 0
        self._records: dict          = {}

    # ── carga ─────────────────────────────────────────────────────────────────

    def load_schema(self, path: str) -> list[str]:
        """
        Carga el esquema SQL con detección automática de encoding.
        Retorna lista de advertencias (ej. PKs compuestas).
        """
        encoding = self._detect_encoding(path)
        with open(path, encoding=encoding, errors="replace") as f:
            self.schema = parse_schema(f.read())
        # NO se crean AVLs aquí — se crean al momento de buscar
        return getattr(self.schema, "_pk_warnings", [])

    # ── detección automática de encoding ─────────────────────────────────────

    @staticmethod
    def _detect_encoding(path: str) -> str:
        """
        Detecta el encoding del archivo leyendo los primeros 8 KB.
        Orden de prioridad:
          1. BOM explícito (UTF-32, UTF-16, UTF-8-BOM)
          2. Heurística ASCII-safe: si todo es ASCII puro → utf-8
          3. Prueba utf-8 estricto
          4. Prueba encodings latinos comunes (cp1252, latin-1, iso-8859-1)
          5. Fallback: latin-1 (nunca falla, acepta cualquier byte)
        """
        with open(path, "rb") as f:
            raw = f.read(8192)

        # BOM
        if raw.startswith(b"\xff\xfe\x00\x00") or raw.startswith(b"\x00\x00\xfe\xff"):
            return "utf-32"
        if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
            return "utf-16"
        if raw.startswith(b"\xef\xbb\xbf"):
            return "utf-8-sig"

        # Intentar utf-8 estricto
        try:
            raw.decode("utf-8")
            return "utf-8"
        except UnicodeDecodeError:
            pass

        # Encodings comunes en español / Europa occidental
        for enc in ("cp1252", "iso-8859-1", "latin-1"):
            try:
                raw.decode(enc)
                return enc
            except UnicodeDecodeError:
                continue

        return "latin-1"   # nunca falla

    @staticmethod
    def _detect_delimiter(path: str, encoding: str) -> str:
        """
        Detecta el delimitador del CSV leyendo las primeras 5 líneas.
        Candidatos: coma, punto y coma, tabulador, pipe, dos puntos.
        Gana el que aparezca más veces de forma consistente.
        Si no puede decidir → coma (estándar RFC 4180).
        """
        candidates = [",", ";", "\t", "|", ":"]
        try:
            with open(path, encoding=encoding, errors="replace") as f:
                lines = [f.readline() for _ in range(5)]
            lines = [l for l in lines if l.strip()]
            if not lines:
                return ","

            # Contar ocurrencias por candidato en cada línea
            scores: dict[str, list[int]] = {d: [] for d in candidates}
            for line in lines:
                for d in candidates:
                    scores[d].append(line.count(d))

            # El delimitador consistente tiene conteo > 0 y baja varianza
            best_delim = ","
            best_score = -1
            for d in candidates:
                counts = scores[d]
                if not counts or max(counts) == 0:
                    continue
                avg = sum(counts) / len(counts)
                # penalizar si las líneas tienen conteos muy distintos
                variance = sum((c - avg) ** 2 for c in counts) / len(counts)
                score = avg - variance * 0.1
                if score > best_score:
                    best_score = score
                    best_delim = d

            return best_delim
        except Exception:
            return ","

    def load_csv(self, path: str) -> list[str]:
        """
        Carga CSV con detección automática de encoding y delimitador.
        Nivel SGBD profesional:

        ENCODING (auto-detectado):
          UTF-8, UTF-8 BOM (Excel), UTF-16, UTF-32,
          Windows-1252, ISO-8859-1 / Latin-1,
          cualquier encoding de 1 byte (fallback latin-1)

        DELIMITADOR (auto-detectado):
          , ; \\t | :   — detecta el más consistente en las primeras 5 líneas

        CABECERA (auto-detectada):
          Se compara la primera fila con los nombres de columna del esquema
          (insensible a mayúsculas y espacios). Si coincide → tiene cabecera.
          Si no coincide → sin cabecera: se mapean las columnas del schema
          en orden posicional. Nunca se usan nombres genéricos col_0, col_1.

        COLUMNAS:
          - Extra en CSV  → ignoradas, aviso
          - Faltantes del esquema → valor vacío, aviso
          - Sin cabecera  → mapeo posicional usando nombres del schema SQL

        FILAS:
          - PK duplicada  → omite la segunda, avisa
          - Error de cast → usa valor vacío, registra en log (no aborta)
          - Fila vacía    → silenciosamente ignorada
          - Fila con menos columnas que el encabezado → rellena con vacío
          - Fila con más columnas que el encabezado → ignora las extra

        RETORNA: lista de strings de advertencia (vacía = todo perfecto)
        """
        if not self.schema:
            raise RuntimeError("Carga el esquema primero")

        warnings: list[str] = []

        # ── 1. Detectar encoding ──────────────────────────────────────────
        encoding = self._detect_encoding(path)

        # ── 2. Detectar delimitador ───────────────────────────────────────
        delimiter = self._detect_delimiter(path, encoding)

        # ── 3. Abrir y leer ───────────────────────────────────────────────
        with open(path, newline="", encoding=encoding, errors="replace") as f:
            # Quitar BOM si quedó como carácter (utf-8-sig no siempre lo quita)
            sample = f.read(3)
            if sample.startswith("\ufeff"):
                sample = sample[1:]
            else:
                f.seek(0)
                sample = ""
            content = sample + f.read()

        # ── 4. Leer primera fila para detectar cabecera ───────────────────
        reader_f   = io.StringIO(content)
        first_row  = next(csv.reader(reader_f, delimiter=delimiter), [])
        schema_names = [c.name for c in self.schema.columns]

        def _normalise(s: str) -> str:
            """Quita espacios, BOM y pasa a minúsculas para comparar."""
            return s.strip().lstrip("\ufeff").lower()

        first_row_norm   = [_normalise(f) for f in first_row]
        schema_names_norm = [_normalise(n) for n in schema_names]

        # Tiene cabecera si al menos la MITAD de los campos de la primera fila
        # coinciden con nombres de columna del schema (comparación insensible).
        # Esto es robusto: funciona aunque el CSV tenga columnas extra o falten.
        if schema_names_norm and first_row_norm:
            schema_set  = set(schema_names_norm)
            matches     = sum(1 for f in first_row_norm if f in schema_set)
            has_header  = matches >= max(1, len(schema_names_norm) // 2)
        else:
            has_header = False

        # ── 5. Construir DictReader con los fieldnames correctos ──────────
        reader_f.seek(0)

        if has_header:
            # La primera fila es la cabecera: DictReader la usa directamente
            reader     = csv.DictReader(reader_f, delimiter=delimiter)
            fieldnames = [_normalise(f) for f in (reader.fieldnames or [])]
            # Re-crear con nombres normalizados para que el mapeo funcione
            reader_f.seek(0)
            reader_f.readline()   # saltar la fila de cabecera original
            reader = csv.DictReader(reader_f,
                                    fieldnames=fieldnames,
                                    delimiter=delimiter)
        else:
            # Sin cabecera: mapear posicionalmente usando nombres del schema.
            # Si el CSV tiene MÁS columnas que el schema → nombres extra col_N.
            n_csv_cols   = len(first_row)
            if n_csv_cols > len(schema_names):
                extra_names = [f"_col_{i}" for i in range(len(schema_names),
                                                           n_csv_cols)]
                fieldnames  = schema_names + extra_names
            else:
                fieldnames = schema_names[:n_csv_cols]

            reader = csv.DictReader(reader_f,
                                    fieldnames=fieldnames,
                                    delimiter=delimiter)
            warnings.append(
                "CSV sin fila de cabecera — columnas mapeadas por posición "
                f"usando el esquema SQL: {', '.join(schema_names)}"
            )

        # ── 6. Verificar cobertura de columnas ────────────────────────────
        schema_cols  = set(schema_names)
        csv_cols_set = set(fieldnames)

        missing = schema_cols - csv_cols_set
        if missing:
            warnings.append(
                f"Columnas del esquema ausentes en el CSV "
                f"(se usará vacío): {', '.join(sorted(missing))}"
            )
        extra = {f for f in csv_cols_set if not f.startswith("_col_")} - schema_cols
        if extra:
            warnings.append(
                f"Columnas del CSV no presentes en el esquema "
                f"(ignoradas): {', '.join(sorted(extra))}"
            )

        if delimiter != ",":
            warnings.append(
                f"Delimitador detectado: '{delimiter}' "
                f"(encoding: {encoding})"
            )
        elif encoding not in ("utf-8", "utf-8-sig"):
            warnings.append(f"Encoding detectado: {encoding}")

        # ── 7. Iterar filas ───────────────────────────────────────────────
        pk_col        = self.schema.pk_column
        dup_pks: int  = 0
        err_rows: int = 0

        for line_num, raw_row in enumerate(reader, start=2):
            # Limpiar nombres de campo de la fila
            row = {
                k.strip().lstrip("\ufeff"): v
                for k, v in (raw_row or {}).items()
                if k is not None
            }

            # Fila completamente vacía → ignorar
            if not any(v and str(v).strip() for v in row.values()):
                continue

            try:
                # Rellenar columnas faltantes con vacío
                for col in self.schema.columns:
                    if col.name not in row:
                        row[col.name] = ""

                casted = self.schema.cast_row(row)
                pk_val = casted.get(pk_col, "")

                # PK vacía → generar una sintética para no perder el registro
                if pk_val == "" or pk_val is None:
                    pk_val = f"__auto_{self.records_loaded}"
                    casted[pk_col] = pk_val
                    if self.records_loaded < 5:
                        warnings.append(
                            f"Fila {line_num}: PK vacía — asignada clave "
                            f"automática '{pk_val}'."
                        )

                # Verificar unicidad de PK antes de almacenar.
                # Equivalente al check de restricción PRIMARY KEY en un SGBD:
                # PostgreSQL: "ERROR: duplicate key value violates unique constraint"
                if pk_val in self._records:
                    dup_pks += 1
                    if dup_pks <= 5:
                        warnings.append(
                            f"Fila {line_num}: ERROR — violación de restricción "
                            f"PRIMARY KEY: la clave duplicada '{pk_val}' ya existe "
                            f"— INSERT rechazado."
                        )
                    continue

                self._store(casted)
                self.records_loaded += 1

            except OverflowError:
                # ── DISCO LLENO: parar la carga inmediatamente ────────────────
                # Comportamiento SGBD profesional: si el medio de almacenamiento
                # está lleno no tiene sentido intentar insertar más filas.
                # El write_record ya hizo rollback del registro parcial.
                warnings.append(
                    f"Fila {line_num}: DISCO LLENO — carga interrumpida. "
                    f"Se cargaron {self.records_loaded} registro(s) correctamente "
                    f"antes de agotar el espacio disponible."
                )
                break   # salir del loop de filas

            except Exception as exc:
                err_rows += 1
                if err_rows <= 5:
                    warnings.append(
                        f"Fila {line_num}: error ({exc}) — omitida."
                    )

        # Resumen final si hubo muchos errores/duplicados
        if dup_pks > 5:
            warnings.append(f"… y {dup_pks - 5} violación(es) de PRIMARY KEY más — INSERT rechazado.")
        if err_rows > 5:
            warnings.append(f"… y {err_rows - 5} fila(s) con error más omitidas.")

        # Advertencias del parser SQL (PKs compuestas, etc.)
        if hasattr(self.schema, "_pk_warnings"):
            warnings = self.schema._pk_warnings + warnings

        return warnings

    def _store(self, row: dict):
        """
        Guarda el registro en disco. No toca ningún AVL (lazy indexing).
        row ya viene casteado por schema.cast_row() desde load_csv,
        así que pk_val tiene el tipo correcto directamente.
        """
        raw    = json.dumps(row, ensure_ascii=False).encode("utf-8")
        pk_col = self.schema.pk_column
        pk_val = row.get(pk_col, "")   # ya casteado — _coerce sería redundante
        if pk_val == "" or pk_val is None:
            pk_val = self._coerce(pk_val)   # fallback si el schema no casteó
        fragments = self.disk.write_record(raw)
        self._records[pk_val] = {
            "record":    row,
            "fragments": fragments,
            "raw_len":   len(raw),
        }

    # ── construcción de índice por demanda ────────────────────────────────────

    def _build_index(self, col: str) -> AVL:
        """
        Construye el AVL de la columna `col` si no existe todavía.
        Si ya existe lo retorna directamente sin reconstruir (lazy indexing).

        Índice primario (col == pk_col) → AVL(unique=True)
            Un nodo por clave, sin duplicados. Idéntico al B-Tree primario
            de PostgreSQL/MySQL: una clave → un puntero a fragments en disco.

        Índice secundario (col != pk_col) → AVL(unique=False)
            Un nodo por valor distinto, cada nodo acumula lista de PKs.
            Equivalente a un índice no-único (CREATE INDEX sin UNIQUE).
        """
        if col in self.indices:
            return self.indices[col]

        pk_col = self.schema.pk_column
        is_pk  = (col == pk_col)
        avl    = AVL(unique=is_pk)

        for pk_val, meta in self._records.items():
            if is_pk:
                # Primario: key=pk_val → value=fragments (un único valor por clave)
                avl.insert(pk_val, meta["fragments"])
            else:
                # Secundario: key=valor_columna → value=pk (acumula PKs)
                attr_val = meta["record"].get(col, "")
                avl.insert(attr_val, pk_val)

        self.indices[col] = avl
        return avl

    def index_exists(self, col: str) -> bool:
        return col in self.indices

    # ── helpers ───────────────────────────────────────────────────────────────

    @staticmethod
    def _coerce(v: Any) -> Any:
        try:    return int(v)
        except (ValueError, TypeError): pass
        try:    return float(v)
        except (ValueError, TypeError): pass
        return str(v)

    def _fetch_by_pk(self, pk_val) -> Optional[dict]:
        """Lee un registro del disco dado su PK."""
        meta = self._records.get(pk_val)
        if meta is None:
            return None
        frags = meta["fragments"]
        raw   = self.disk.read_record(frags)
        try:    record = json.loads(raw.decode("utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            record = {"_raw": raw.hex()}

        addr_info = []
        for pid, slot_idx in frags:
            addr = self.disk.linear_to_address(pid)
            page = self.disk.get_page(pid)
            addr_info.append({
                "page_id":      pid,
                "slot_idx":     slot_idx,
                "plato":        addr.platter,
                "superficie":   addr.surface,
                "pista":        addr.track,
                "sector":       addr.sector,
                "slots_en_pag": page.slot_count if page else 0,
            })
        return {"pk": pk_val, "record": record,
                "direcciones": addr_info, "raw_len": len(raw)}

    # ── búsquedas (construyen el índice si no existe) ─────────────────────────

    def _cast_for_col(self, col: str, value: str) -> Any:
        """
        Castea `value` al tipo real de la columna según el esquema.
        Más preciso que _coerce: evita que "0123" se convierta a 123.
        """
        col_def = next((c for c in self.schema.columns
                        if c.name == col), None)
        if col_def:
            return col_def.cast(value)
        return self._coerce(value)   # fallback si la columna no está en schema

    def search(self, col: str, value: str) -> list[dict]:
        """Búsqueda exacta. Construye el AVL de `col` si no existe."""
        if not self.schema or col not in self.columns:
            return []
        pk_col  = self.schema.pk_column
        coerced = self._cast_for_col(col, value)   # usa el tipo del schema
        avl     = self._build_index(col)            # lazy: crea o reutiliza
        values  = avl.search(coerced)
        if not values:
            return []

        if col == pk_col:
            result = self._fetch_by_pk(coerced)
            return [result] if result else []
        else:
            out = []; seen = set()
            for pk in values:
                if pk not in seen:
                    seen.add(pk)
                    r = self._fetch_by_pk(pk)
                    if r: out.append(r)
            return out

    def range_search(self, col: str, lo: str, hi: str) -> list[dict]:
        """Búsqueda por rango. Construye el AVL de `col` si no existe."""
        if not self.schema or col not in self.columns:
            return []
        pk_col = self.schema.pk_column
        lo_v   = self._cast_for_col(col, lo)   # usa el tipo del schema
        hi_v   = self._cast_for_col(col, hi)   # usa el tipo del schema
        avl    = self._build_index(col)         # lazy: crea o reutiliza
        hits   = avl.range_search(lo_v, hi_v)

        out = []; seen = set()
        for key, values in hits:
            if col == pk_col:
                if key not in seen:
                    seen.add(key)
                    r = self._fetch_by_pk(key)
                    if r: out.append(r)
            else:
                for pk in values:
                    if pk not in seen:
                        seen.add(pk)
                        r = self._fetch_by_pk(pk)
                        if r: out.append(r)
        return out

    @property
    def columns(self) -> list[str]:
        return [c.name for c in self.schema.columns] if self.schema else []

    @property
    def pk_column(self) -> Optional[str]:
        return self.schema.pk_column if self.schema else None


# ══════════════════════════════════════════════════════════════════════════════
#  APLICACIÓN
# ══════════════════════════════════════════════════════════════════════════════

class App(ctk.CTk):

    def __init__(self):
        super().__init__()
        self.title("Simulador de Almacenamiento Físico de Base de Datos")
        self.geometry("1380x860")
        self.minsize(1100, 700)
        self.configure(fg_color=BG)

        self.disk: Optional[Disk]            = None
        self.db:   Optional[DatabaseManager] = None
        self._highlighted_pks: set           = set()
        self._sector_items:    dict          = {}
        self._col_var = tk.StringVar(value="")

        self._build_ui()

    # ──────────────────────────────────────────────────────────────────────────
    #  CONSTRUCCIÓN UI
    # ──────────────────────────────────────────────────────────────────────────

    def _build_ui(self):
        self.grid_columnconfigure(0, weight=0, minsize=440)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self._build_left()
        self._build_right()

    def _build_left(self):
        left = ctk.CTkScrollableFrame(self, fg_color=BG, width=440)
        left.grid(row=0, column=0, sticky="nsew", padx=(12,6), pady=12)
        left.grid_columnconfigure(0, weight=1)
        r = 0

        ctk.CTkLabel(left, text="SIMULADOR DE DISCO",
                     font=("Consolas",16,"bold"),
                     text_color=ACCENT).grid(
            row=r, column=0, sticky="w", pady=(0,2)); r+=1
        ctk.CTkLabel(left,
                     text="Avance 1 — Modelado del Problema  |  Slotted Pages",
                     font=FL, text_color=MUTED).grid(
            row=r, column=0, sticky="w", pady=(0,14)); r+=1

        # ── Sección 1: Geometría ──────────────────────────────────────────────
        r = self._section(left, r, "① GEOMETRÍA DEL DISCO",
                          ACCENT, ACCENT_D, ACCENT_H)

        self._vp = tk.IntVar(value=2)
        self._vt = tk.IntVar(value=4)
        self._vs = tk.IntVar(value=8)
        self._vb = tk.IntVar(value=64)

        for label, var in [
            ("Número de platos",             self._vp),
            ("Pistas por superficie",        self._vt),
            ("Sectores por pista",           self._vs),
            ("Capacidad del sector (bytes)", self._vb),
        ]:
            r = self._num_input(left, r, label, var)

        ctk.CTkLabel(
            left,
            text=(f"ℹ  Slotted pages: varios registros comparten\n"
                  f"   una misma página. Sin padding desperdiciado.\n"
                  f"   Header fijo: {PAGE_HDR_SIZE}B | Slot: {SLOT_SIZE}B c/u"),
            font=("Consolas",8), text_color=MUTED,
            justify="left").grid(row=r, column=0, sticky="w", pady=(0,6)); r+=1

        self._sum_frame = ctk.CTkFrame(left, fg_color=DARK,
                                       corner_radius=6,
                                       border_width=1, border_color=BORDER)
        self._sum_frame.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1
        self._sum_frame.grid_columnconfigure(1, weight=1)
        self._sum_lbls: dict = {}
        for i, key in enumerate(["Superficies","Total páginas",
                                  "Usable / página","Capacidad total"]):
            ctk.CTkLabel(self._sum_frame, text=key, font=FL,
                         text_color=MUTED).grid(
                row=i, column=0, padx=10, pady=2, sticky="w")
            v = ctk.CTkLabel(self._sum_frame, text="—",
                             font=FMS, text_color=ACCENT)
            v.grid(row=i, column=1, padx=10, pady=2, sticky="e")
            self._sum_lbls[key] = v

        for var in (self._vp, self._vt, self._vs, self._vb):
            var.trace_add("write", lambda *_: self._refresh_summary())
        self._refresh_summary()

        ctk.CTkButton(left, text="Configurar disco →",
                      fg_color=ACCENT_D, text_color=ACCENT,
                      border_color=ACCENT, border_width=1,
                      hover_color=ACCENT_H, font=FT,
                      command=self._cmd_configure).grid(
            row=r, column=0, sticky="ew", pady=(0,12)); r+=1

        # ── Sección 2: Archivos ───────────────────────────────────────────────
        r = self._section(left, r, "② ESQUEMA (.txt) Y DATOS (.csv)",
                          YELLOW, YELLOW_D, YELLOW_H)

        self._txt_path = None
        self._csv_path = None
        r = self._file_row(left, r, "Esquema SQL (.txt)", ".txt",
                           "_txt_path", "_lbl_txt")
        r = self._file_row(left, r, "Datos (.csv)", ".csv",
                           "_csv_path", "_lbl_csv")

        ctk.CTkButton(left, text="Cargar →",
                      fg_color=YELLOW_D, text_color=YELLOW,
                      border_color=YELLOW, border_width=1,
                      hover_color=YELLOW_H, font=FT,
                      command=self._cmd_load).grid(
            row=r, column=0, sticky="ew", pady=(4,6)); r+=1

        self._schema_lbl = ctk.CTkLabel(left, text="", font=FMS,
                                        text_color=GREEN,
                                        wraplength=420, justify="left")
        self._schema_lbl.grid(row=r, column=0, sticky="w", pady=(0,8)); r+=1

        # ── Sección 3: Búsqueda ───────────────────────────────────────────────
        r = self._section(left, r, "③ BÚSQUEDA",
                          GREEN, GREEN_D, GREEN_H)

        # Selector de columna
        ctk.CTkLabel(left, text="Buscar por columna:",
                     font=FL, text_color=MUTED).grid(
            row=r, column=0, sticky="w", pady=(0,2)); r+=1

        self._col_menu = ctk.CTkOptionMenu(
            left, variable=self._col_var,
            values=["— carga datos primero —"],
            fg_color=DARK, button_color=ACCENT_D,
            button_hover_color=ACCENT_H,
            text_color=TEXT, font=FM,
            command=lambda _: self._draw_avl())
        self._col_menu.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1

        ctk.CTkLabel(left, text="Valor exacto:",
                     font=FL, text_color=MUTED).grid(
            row=r, column=0, sticky="w", pady=(0,2)); r+=1

        fe = ctk.CTkFrame(left, fg_color="transparent")
        fe.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1
        fe.grid_columnconfigure(0, weight=1)
        self._e_exact = ctk.CTkEntry(fe,
                                     placeholder_text="ej: 3  o  García",
                                     font=FM, fg_color=DARK,
                                     border_color=BORDER)
        self._e_exact.grid(row=0, column=0, sticky="ew", padx=(0,6))
        ctk.CTkButton(fe, text="Buscar", width=70,
                      fg_color=GREEN_D, text_color=GREEN,
                      border_color=GREEN, border_width=1,
                      hover_color=GREEN_H, font=FT,
                      command=self._cmd_exact).grid(row=0, column=1)

        ctk.CTkLabel(left,
                     text="Rango [desde — hasta]  "
                          "(strings: orden alfabético):",
                     font=FL, text_color=MUTED).grid(
            row=r, column=0, sticky="w", pady=(0,2)); r+=1

        fr2 = ctk.CTkFrame(left, fg_color="transparent")
        fr2.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1
        fr2.grid_columnconfigure((0,1), weight=1)
        self._e_from = ctk.CTkEntry(fr2, placeholder_text="desde",
                                    font=FM, fg_color=DARK,
                                    border_color=BORDER)
        self._e_from.grid(row=0, column=0, sticky="ew", padx=(0,4))
        self._e_to = ctk.CTkEntry(fr2, placeholder_text="hasta",
                                  font=FM, fg_color=DARK,
                                  border_color=BORDER)
        self._e_to.grid(row=0, column=1, sticky="ew", padx=(0,4))
        ctk.CTkButton(fr2, text="Buscar", width=70,
                      fg_color=GREEN_D, text_color=GREEN,
                      border_color=GREEN, border_width=1,
                      hover_color=GREEN_H, font=FT,
                      command=self._cmd_range).grid(row=0, column=2)

        ctk.CTkLabel(left, text="Resultados:",
                     font=FL, text_color=MUTED).grid(
            row=r, column=0, sticky="w", pady=(0,2)); r+=1

        self._result_box = ctk.CTkTextbox(
            left, height=200, font=FMS,
            fg_color=DARK, text_color=TEXT,
            border_color=BORDER, border_width=1)
        self._result_box.grid(row=r, column=0, sticky="ew",
                              pady=(0,12)); r+=1

        # ── Log ───────────────────────────────────────────────────────────────
        r = self._section(left, r, "LOG DEL SISTEMA", MUTED, MUTED_D, BORDER)

        self._log_box = ctk.CTkTextbox(left, height=110, font=FMS,
                                       fg_color=DARK, text_color=MUTED,
                                       border_color=BORDER, border_width=1)
        self._log_box.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1

        ctk.CTkButton(left, text="⟳  Reiniciar",
                      fg_color=RED_D, text_color=RED,
                      border_color=RED, border_width=1,
                      hover_color=RED_H, font=FT,
                      command=self._cmd_reset).grid(
            row=r, column=0, sticky="ew")

    def _build_right(self):
        right = ctk.CTkFrame(self, fg_color=BG)
        right.grid(row=0, column=1, sticky="nsew", padx=(6,12), pady=12)
        right.grid_rowconfigure(1, weight=2)
        right.grid_rowconfigure(3, weight=1)
        right.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            right,
            text="MAPA DEL DISCO  ·  Plato › Superficie › Pista › Página"
                 "   (hover = info   click = detalle)",
            font=FT, text_color=ACCENT).grid(
            row=0, column=0, sticky="w", pady=(0,4))

        # Canvas con scrollbars
        cf = tk.Frame(right, bg=BG)
        cf.grid(row=1, column=0, sticky="nsew", pady=(0,10))
        cf.grid_rowconfigure(0, weight=1)
        cf.grid_columnconfigure(0, weight=1)

        self._disk_canvas = tk.Canvas(cf, bg=PANEL, highlightthickness=0)
        self._disk_canvas.grid(row=0, column=0, sticky="nsew")

        vsb = tk.Scrollbar(cf, orient="vertical",
                           command=self._disk_canvas.yview)
        vsb.grid(row=0, column=1, sticky="ns")
        hsb = tk.Scrollbar(cf, orient="horizontal",
                           command=self._disk_canvas.xview)
        hsb.grid(row=1, column=0, sticky="ew")
        self._disk_canvas.configure(yscrollcommand=vsb.set,
                                    xscrollcommand=hsb.set)
        self._disk_canvas.bind(
            "<MouseWheel>",
            lambda e: self._disk_canvas.yview_scroll(
                -1 if e.delta > 0 else 1, "units"))
        self._disk_canvas.bind("<Motion>",   self._on_hover)
        self._disk_canvas.bind("<Leave>",    lambda e: self._hide_tip())
        self._disk_canvas.bind("<Button-1>", self._on_click)

        # Tooltip
        self._tip = tk.Toplevel(self)
        self._tip.withdraw()
        self._tip.overrideredirect(True)
        self._tip.configure(bg="#0d1e30")
        self._tip_lbl = tk.Label(self._tip, bg="#0d1e30", fg=TEXT,
                                 font=("Consolas",9), padx=8, pady=5,
                                 justify="left")
        self._tip_lbl.pack()

        ctk.CTkLabel(right,
                     text="ÁRBOL AVL  ·  columna seleccionada",
                     font=FT, text_color=ACCENT2).grid(
            row=2, column=0, sticky="w", pady=(0,4))

        self._avl_canvas = tk.Canvas(right, bg=PANEL,
                                     highlightthickness=0, height=200)
        self._avl_canvas.grid(row=3, column=0, sticky="nsew")

    # ──────────────────────────────────────────────────────────────────────────
    #  HELPERS UI
    # ──────────────────────────────────────────────────────────────────────────

    def _section(self, parent, row, text, color, bg, hover):
        frame = ctk.CTkFrame(parent, fg_color=bg, corner_radius=4,
                             border_width=1, border_color=hover)
        frame.grid(row=row, column=0, sticky="ew", pady=(8,6))
        ctk.CTkLabel(frame, text=text, font=FT,
                     text_color=color).pack(anchor="w", padx=10, pady=5)
        return row + 1

    def _num_input(self, parent, row, label, var):
        ctk.CTkLabel(parent, text=label, font=FL, text_color=MUTED).grid(
            row=row, column=0, sticky="w", pady=(0,2))
        row += 1
        ctk.CTkEntry(parent, textvariable=var, font=FM,
                     fg_color=DARK, border_color=BORDER).grid(
            row=row, column=0, sticky="ew", pady=(0,6))
        return row + 1

    def _file_row(self, parent, row, label, ext, path_attr, lbl_attr):
        setattr(self, path_attr, None)
        ctk.CTkLabel(parent, text=label, font=FL, text_color=MUTED).grid(
            row=row, column=0, sticky="w", pady=(0,2))
        row += 1
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        frame.grid(row=row, column=0, sticky="ew", pady=(0,6))
        frame.grid_columnconfigure(1, weight=1)
        row += 1

        def browse(pa=path_attr, la=lbl_attr, ex=ext):
            path = filedialog.askopenfilename(
                filetypes=[(f"Archivo {ex}", f"*{ex}"), ("Todos","*.*")])
            if path:
                setattr(self, pa, path)
                short = path.replace("\\","/").split("/")[-1]
                getattr(self, la).configure(text=short, text_color=GREEN)

        ctk.CTkButton(frame, text=f"📂 {ext}", width=80,
                      fg_color=YELLOW_D, text_color=YELLOW,
                      border_color=YELLOW, border_width=1,
                      hover_color=YELLOW_H, font=FL,
                      command=browse).grid(row=0, column=0, padx=(0,8))
        lbl_w = ctk.CTkLabel(frame, text="ningún archivo",
                             font=FMS, text_color=MUTED, anchor="w")
        lbl_w.grid(row=0, column=1, sticky="ew")
        setattr(self, lbl_attr, lbl_w)
        return row

    def _log(self, msg: str, color: str = MUTED):
        self._log_box.configure(state="normal")
        self._log_box.insert("end", f"> {msg}\n")
        self._log_box.see("end")
        self._log_box.configure(state="disabled")

    def _refresh_summary(self):
        try:
            p=self._vp.get(); t=self._vt.get()
            s=self._vs.get(); b=self._vb.get()
            surf  = p*2; total = surf*t*s
            usable= max(0, b - PAGE_HDR_SIZE)
            cap   = total*b/1024
            self._sum_lbls["Superficies"].configure(text=str(surf))
            self._sum_lbls["Total páginas"].configure(text=f"{total:,}")
            self._sum_lbls["Usable / página"].configure(
                text=f"{usable}B  (página {b}B − hdr {PAGE_HDR_SIZE}B)")
            self._sum_lbls["Capacidad total"].configure(text=f"{cap:.1f} KB")
        except Exception: pass

    def _show_results(self, results: list[dict], title: str):
        self._result_box.configure(state="normal")
        self._result_box.delete("1.0","end")
        self._result_box.insert("end", f"{'─'*48}\n{title}\n{'─'*48}\n")

        if not results:
            self._result_box.insert("end", "  Sin resultados.\n")
        else:
            for item in results:
                self._result_box.insert("end", "\n")
                for k, v in item["record"].items():
                    self._result_box.insert("end", f"  {k}: {v}\n")
                self._result_box.insert("end", f"  {'─'*30}\n")
                for d in item["direcciones"]:
                    self._result_box.insert(
                        "end",
                        f"  Fragmento en página {d['page_id']} "
                        f"(slot {d['slot_idx']}):\n"
                        f"    Plato {d['plato']}  ·  "
                        f"Superficie {d['superficie']}  ·  "
                        f"Pista {d['pista']:03d}  ·  "
                        f"Sector {d['sector']:03d}\n"
                        f"    Slots en esta página: {d['slots_en_pag']}\n")
                self._result_box.insert("end", f"  {'─'*30}\n")

        self._result_box.configure(state="disabled")

    # ──────────────────────────────────────────────────────────────────────────
    #  COMANDOS
    # ──────────────────────────────────────────────────────────────────────────

    def _cmd_configure(self):
        try:
            if self.disk:
                self.disk.close()   # cerrar disco anterior
            cfg = DiskConfig(self._vp.get(), self._vt.get(),
                             self._vs.get(), self._vb.get())
            if cfg.usable_bytes < SLOT_SIZE + 1:
                messagebox.showerror("Error",
                    f"Página demasiado pequeña. Mínimo "
                    f"{PAGE_HDR_SIZE + SLOT_SIZE + 1}B.")
                return
            self.disk = Disk(cfg)
            self._sector_items = {}
            self._log(f"Disco configurado: {cfg.total_sectors:,} páginas · "
                      f"usable={cfg.usable_bytes}B/página", ACCENT)
            self._draw_disk()
        except Exception as ex:
            messagebox.showerror("Error", str(ex))

    def _cmd_load(self):
        if not self.disk:
            messagebox.showwarning("Aviso","Configura el disco primero"); return
        if not self._txt_path:
            messagebox.showwarning("Aviso","Selecciona el esquema (.txt)"); return
        if not self._csv_path:
            messagebox.showwarning("Aviso","Selecciona los datos (.csv)"); return
        try:
            self.disk.close()
            self.disk = Disk(self.disk.config)
            self.db   = DatabaseManager(self.disk)
            schema_warnings = self.db.load_schema(self._txt_path)
            sch = self.db.schema
            cols_txt = "  ".join(
                f"{'[PK]' if c.is_pk else ''}{c.name}:{c.py_type.__name__}"
                for c in sch.columns)
            self._schema_lbl.configure(
                text=f"Tabla: {sch.name}  |  PK: {sch.pk_column}\n{cols_txt}")
            n_cols = len(sch.columns)
            self._log(
                f"Esquema: '{sch.name}'  PK='{sch.pk_column}'  "
                f"→  {n_cols} columnas detectadas", GREEN)
            for w in schema_warnings:
                self._log(f"⚠  {w}", YELLOW)

            csv_warnings = self.db.load_csv(self._csv_path)
            all_warnings = schema_warnings + csv_warnings
            pages = self.disk.pages_used()
            self._log(f"{self.db.records_loaded} registros  ·  "
                      f"{pages} página(s) usada(s)", GREEN)

            # Mostrar advertencias (columnas faltantes, PKs duplicadas, encoding, etc.)
            if csv_warnings:
                for w in csv_warnings:
                    self._log(f"⚠  {w}", YELLOW)
            if all_warnings:
                messagebox.showwarning(
                    "Advertencias al cargar",
                    "\n\n".join(all_warnings)
                )
            # estadísticas de ocupación
            occ_list = [self.disk.get_page(i).occupancy_pct
                        for i in range(pages)]
            avg_occ = sum(occ_list)/len(occ_list) if occ_list else 0
            self._log(f"Ocupación promedio de páginas: {avg_occ:.1f}%", ACCENT)

            self._highlighted_pks = set()
            # poblar selector de columnas (todos los atributos)
            cols = self.db.columns
            self._col_menu.configure(values=cols)
            self._col_var.set(self.db.pk_column or cols[0])
            self._draw_disk()
            self._draw_avl()   # mostrará "índice no existe aún"
        except Exception as ex:
            messagebox.showerror("Error al cargar", str(ex))
            self._log(f"ERROR: {ex}", RED)

    def _cmd_exact(self):
        if not self.db:
            messagebox.showwarning("Aviso","Carga los datos primero"); return
        col = self._col_var.get()
        val = self._e_exact.get().strip()
        if not val or col.startswith("—"): return
        try:
            results = self.db.search(col, val)
            self._highlighted_pks = {r["pk"] for r in results}
            self._show_results(results, f"Exacta  [{col}] = {val}")
            self._draw_disk(); self._draw_avl()
            self._log(f"Exacta [{col}='{val}'] → {len(results)} resultado(s)",
                      GREEN)
        except Exception as ex:
            self._log(f"Error: {ex}", RED)

    def _cmd_range(self):
        if not self.db:
            messagebox.showwarning("Aviso","Carga los datos primero"); return
        col = self._col_var.get()
        lo  = self._e_from.get().strip()
        hi  = self._e_to.get().strip()
        if not lo or not hi or col.startswith("—"): return
        try:
            results = self.db.range_search(col, lo, hi)
            self._highlighted_pks = {r["pk"] for r in results}
            self._show_results(results, f"Rango  [{col}] ∈ [{lo}, {hi}]")
            self._draw_disk(); self._draw_avl()
            self._log(f"Rango [{col}] [{lo},{hi}] → "
                      f"{len(results)} resultado(s)", GREEN)
        except Exception as ex:
            self._log(f"Error: {ex}", RED)

    def _cmd_reset(self):
        if self.disk:
            self.disk.close()   # flush + cerrar archivo
        self.disk = None; self.db = None
        self._highlighted_pks = set(); self._sector_items = {}
        self._disk_canvas.delete("all"); self._avl_canvas.delete("all")
        self._result_box.configure(state="normal")
        self._result_box.delete("1.0","end")
        self._result_box.configure(state="disabled")
        self._schema_lbl.configure(text="")
        self._lbl_txt.configure(text="ningún archivo", text_color=MUTED)
        self._lbl_csv.configure(text="ningún archivo", text_color=MUTED)
        self._txt_path = self._csv_path = None
        self._col_menu.configure(values=["— carga datos primero —"])
        self._col_var.set("— carga datos primero —")
        self._log("Sistema reiniciado.", MUTED)

    # ──────────────────────────────────────────────────────────────────────────
    #  DIBUJO: MAPA DEL DISCO
    # ──────────────────────────────────────────────────────────────────────────

    def _draw_disk(self):
        c = self._disk_canvas
        c.delete("all")
        self._sector_items = {}
        if not self.disk: return

        cfg     = self.disk.config
        SW      = 16; SH = 16; SG = 2
        TRACK_H = SH + SG
        PAD     = 10; LABEL_W = 50

        # pid → set de pks que tienen fragmentos en esa página
        pid_pks: dict[int, set] = {}
        if self.db:
            for pk, meta in self.db._records.items():
                for pid, _ in meta["fragments"]:
                    pid_pks.setdefault(pid, set()).add(pk)

        hl      = self._highlighted_pks
        total_w = max(600, PAD + LABEL_W +
                      cfg.sectors_per_track*(SW+SG) + PAD + 20)
        y = PAD

        for pi in range(cfg.platters):
            pc  = PLATTER[pi % len(PLATTER)]
            pcd = PLATTER_D[pi % len(PLATTER_D)]

            rows_h = 2*cfg.tracks_per_surface*TRACK_H + 2*6 + 22
            c.create_rectangle(PAD, y, total_w-PAD, y+rows_h,
                               fill="#0d1a28", outline=pc, width=1)
            c.create_text(PAD+8, y+5, anchor="nw",
                          text=f"PLATO {pi}", fill=pc,
                          font=("Consolas",9,"bold"))
            y += 20

            for si in range(2):
                c.create_text(PAD+8, y, anchor="nw",
                              text=f"  SUP {si}  "
                                   f"{'cara superior' if si==0 else 'cara inferior'}",
                              fill=MUTED, font=("Consolas",8))
                y += 13

                for ti in range(cfg.tracks_per_surface):
                    c.create_text(PAD+4, y+SH//2, anchor="w",
                                  text=f"T{ti:02d}", fill=pc,
                                  font=("Consolas",8))
                    x = PAD + LABEL_W

                    for seci in range(cfg.sectors_per_track):
                        sg_i = pi*2 + si
                        tg   = sg_i*cfg.tracks_per_surface + ti
                        pid  = tg*cfg.sectors_per_track + seci

                        page = self.disk.get_page(pid)
                        pks  = pid_pks.get(pid, set())
                        hi   = bool(pks & hl)

                        if page and page.slot_count > 0:
                            occ = page.occupancy_pct
                            if hi:
                                bg_col = YELLOW; ol_col = YELLOW
                            elif occ >= 99.9:
                                bg_col = pc; ol_col = pc
                            else:
                                bg_col = pcd; ol_col = pc

                            item = c.create_rectangle(
                                x, y, x+SW, y+SH,
                                fill=bg_col, outline=ol_col, width=1)

                            # barra de ocupación
                            bar_h   = max(2, int(SH * occ / 100))
                            bar_col = (YELLOW if hi
                                       else (GREEN if occ >= 99.9 else ORANGE))
                            c.create_rectangle(
                                x+1, y+SH-bar_h, x+SW-1, y+SH-1,
                                fill=bar_col, outline="")

                            # indicador multi-registro
                            if len(pks) > 1:
                                c.create_rectangle(
                                    x+SW-4, y, x+SW, y+4,
                                    fill=ACCENT2, outline="")

                            info = {"pid": pid, "page": page,
                                    "pks": pks, "occ": occ,
                                    "pi": pi, "si": si,
                                    "ti": ti, "seci": seci}
                        elif page:
                            # página abierta pero vacía (primera página)
                            item = c.create_rectangle(
                                x, y, x+SW, y+SH,
                                fill="#1a2d40", outline=BORDER, width=1)
                            info = None
                        else:
                            # página no asignada
                            item = c.create_rectangle(
                                x, y, x+SW, y+SH,
                                fill="#0d1520", outline="#131f30", width=1)
                            info = None

                        self._sector_items[item] = {
                            "pid": pid, "pi": pi, "si": si,
                            "ti": ti, "seci": seci, "info": info,
                        }
                        x += SW + SG
                    y += TRACK_H
                y += 6
            y += 12

        # Leyenda
        leg = [(PLATTER[0],"Llena 100%"),
               (PLATTER_D[0],"Parcial"),
               (YELLOW,"Resultado"),
               ("#1a2d40","Libre"),
               ("#0d1520","No asignada")]
        lx = PAD
        for fill, txt in leg:
            c.create_rectangle(lx, y+2, lx+10, y+12, fill=fill, outline="")
            c.create_text(lx+14, y+2, anchor="nw", text=txt,
                          fill=MUTED, font=("Consolas",8))
            lx += len(txt)*6 + 26
        c.create_rectangle(lx, y+2, lx+10, y+12, fill=ACCENT2, outline="")
        c.create_text(lx+14, y+2, anchor="nw", text="Multi-reg",
                      fill=MUTED, font=("Consolas",8))
        y += 20
        c.configure(scrollregion=(0, 0, total_w, y+PAD))

    # ──────────────────────────────────────────────────────────────────────────
    #  HOVER Y CLICK
    # ──────────────────────────────────────────────────────────────────────────

    def _find_item(self, event) -> Optional[int]:
        cx = self._disk_canvas.canvasx(event.x)
        cy = self._disk_canvas.canvasy(event.y)
        items = self._disk_canvas.find_overlapping(cx-1,cy-1,cx+1,cy+1)
        for it in items:
            if it in self._sector_items: return it
        return None

    def _on_hover(self, event):
        it = self._find_item(event)
        if not it: self._hide_tip(); return
        d    = self._sector_items[it]
        info = d["info"]
        if info:
            pks_str = ", ".join(str(p) for p in sorted(info["pks"]))
            txt = (f"Página {d['pid']}  |  {info['occ']}% ocupada\n"
                   f"P{d['pi']}·S{d['si']}·T{d['ti']:02d}·Sec{d['seci']:02d}\n"
                   f"Slots: {info['page'].slot_count}  |  "
                   f"Libre: {info['page'].free_space}B\n"
                   f"Registros: {pks_str}\n"
                   f"Click para detalles →")
        else:
            txt = (f"Página {d['pid']}  —  Libre / no asignada\n"
                   f"P{d['pi']}·S{d['si']}·T{d['ti']:02d}·Sec{d['seci']:02d}")
        self._tip_lbl.configure(text=txt)
        self._tip.deiconify()
        self._tip.geometry(
            f"+{self.winfo_rootx()+event.x+16}"
            f"+{self.winfo_rooty()+event.y+16}")

    def _hide_tip(self):
        self._tip.withdraw()

    def _on_click(self, event):
        it = self._find_item(event)
        if it:
            d = self._sector_items[it]
            self._popup_page(d["pid"], d["pi"], d["si"],
                             d["ti"], d["seci"], d["info"])

    # ──────────────────────────────────────────────────────────────────────────
    #  POPUP DETALLE DE PÁGINA
    # ──────────────────────────────────────────────────────────────────────────

    def _popup_page(self, pid, pi, si, ti, seci, info):
        pop = tk.Toplevel(self)
        pop.title(f"Página {pid}  P{pi}·S{si}·T{ti:02d}·Sec{seci:02d}")
        pop.configure(bg=PANEL)
        pop.resizable(True, True)
        pop.geometry("640x560")
        pop.minsize(500, 320)

        pop.wait_visibility()

        pop.grab_set()

        # ── Contenedor scrollable ──────────────────────────────────────────
        outer = tk.Frame(pop, bg=PANEL)
        outer.pack(fill="both", expand=True)
        outer.grid_rowconfigure(0, weight=1)
        outer.grid_columnconfigure(0, weight=1)

        _canvas = tk.Canvas(outer, bg=PANEL, highlightthickness=0)
        _vsb    = tk.Scrollbar(outer, orient="vertical", command=_canvas.yview)
        _hsb    = tk.Scrollbar(outer, orient="horizontal", command=_canvas.xview)
        _canvas.configure(yscrollcommand=_vsb.set, xscrollcommand=_hsb.set)

        _vsb.grid(row=0, column=1, sticky="ns")
        _hsb.grid(row=1, column=0, sticky="ew")
        _canvas.grid(row=0, column=0, sticky="nsew")

        # Frame interior donde va todo el contenido
        inner = tk.Frame(_canvas, bg=PANEL)
        win_id = _canvas.create_window((0, 0), window=inner, anchor="nw")

        def _on_inner_configure(e):
            _canvas.configure(scrollregion=_canvas.bbox("all"))
        def _on_canvas_configure(e):
            _canvas.itemconfig(win_id, width=e.width)
        inner.bind("<Configure>", _on_inner_configure)
        _canvas.bind("<Configure>", _on_canvas_configure)

        # Scroll con rueda del ratón
        def _on_wheel(e):
            _canvas.yview_scroll(-1 if e.delta > 0 else 1, "units")
        _canvas.bind("<MouseWheel>", _on_wheel)
        inner.bind("<MouseWheel>",   _on_wheel)

        sz     = self.disk.config.sector_size_bytes
        usable = self.disk.config.usable_bytes

        def rlbl(txt, fg=TEXT, font=("Consolas",10)):
            tk.Label(inner, text=txt, bg=PANEL, fg=fg,
                     font=font, anchor="w").pack(fill="x", padx=20, pady=2)

        def sep():
            tk.Frame(inner, bg=BORDER, height=1).pack(fill="x", padx=20, pady=6)

        rlbl("DETALLE DE PÁGINA (SECTOR)", fg=ACCENT,
             font=("Consolas",13,"bold"))
        rlbl(f"Página {pid}  ·  Plato {pi}  ·  Sup {si}  ·  "
             f"Pista {ti:02d}  ·  Sector {seci:02d}",
             fg=MUTED, font=("Consolas",9))
        sep()

        if not info:
            rlbl("Estado:  LIBRE / NO ASIGNADA", fg=MUTED)
            rlbl(f"Tamaño total: {sz} B")
            rlbl(f"  Page header:  {PAGE_HDR_SIZE} B")
            rlbl(f"  Usable:       {usable} B")
        else:
            page = info["page"]
            occ  = info["occ"]
            used = page.free_ptr - PAGE_HDR_SIZE
            free = page.free_space
            pks  = sorted(info["pks"])

            rlbl(f"Ocupación: {occ}%   |   "
                 f"{used}B usados   |   {free}B libres",
                 fg=GREEN if occ >= 99 else YELLOW,
                 font=("Consolas",10,"bold"))
            rlbl(f"Slots usados: {page.slot_count}   |   "
                 f"next_page: "
                 f"{'—' if page.next_page==NO_PAGE else page.next_page}",
                 fg=MUTED, font=("Consolas",9))
            sep()

            # Barra visual de la página (se adapta al ancho)
            rlbl("ESTRUCTURA DE LA PÁGINA:", fg=MUTED,
                 font=("Consolas",9,"bold"))
            BAR_W = 560
            sc = tk.Canvas(inner, width=BAR_W, height=54,
                           bg=PANEL, highlightthickness=0)
            sc.pack(padx=20, pady=4, anchor="w")

            # header
            hw = int(BAR_W * PAGE_HDR_SIZE / sz)
            sc.create_rectangle(0,6,hw,48, fill="#1a2d40", outline=ACCENT)
            sc.create_text(hw//2, 27, text=f"HDR\n{PAGE_HDR_SIZE}B",
                           fill=ACCENT, font=("Consolas",7,"bold"))

            # slots de datos (colores alternos)
            colors_slot = [GREEN, ORANGE, ACCENT2, YELLOW, RED]
            slot_x = hw
            for i, (off, ln) in enumerate(page.slots):
                sw2 = max(1, int(BAR_W * ln / sz))
                col = colors_slot[i % len(colors_slot)]
                sc.create_rectangle(slot_x, 6, slot_x+sw2, 48,
                                    fill=col, outline=DARK)
                if sw2 > 14:
                    sc.create_text(slot_x+sw2//2, 27,
                                   text=f"S{i}\n{ln}B",
                                   fill=DARK, font=("Consolas",7,"bold"))
                slot_x += sw2

            # espacio libre
            free_x = hw + int(BAR_W * used / sz)
            free_w = BAR_W - free_x - int(BAR_W * page.slot_count * SLOT_SIZE / sz)
            if free_w > 0:
                sc.create_rectangle(free_x, 6, free_x+free_w, 48,
                                    fill="#1a2d40", outline=BORDER)
                if free_w > 30:
                    sc.create_text(free_x+free_w//2, 27,
                                   text=f"libre\n{free}B",
                                   fill=MUTED, font=("Consolas",7))

            # slot directory (al final)
            sd_w = int(BAR_W * page.slot_count * SLOT_SIZE / sz)
            if sd_w > 0:
                sc.create_rectangle(BAR_W-sd_w, 6, BAR_W, 48,
                                    fill="#2a1545", outline=ACCENT2)
                if sd_w > 20:
                    sc.create_text(BAR_W-sd_w//2, 27,
                                   text=f"dir\n{page.slot_count*SLOT_SIZE}B",
                                   fill=ACCENT2, font=("Consolas",7))

            sep()

            # Detalle por slot
            rlbl("SLOTS:", fg=MUTED, font=("Consolas",9,"bold"))
            if self.db:
                slot_pks: dict[tuple,str] = {}
                for pk, meta in self.db._records.items():
                    for fpid, fslot in meta["fragments"]:
                        if fpid == pid:
                            slot_pks[(fpid, fslot)] = pk

            for i, (off, ln) in enumerate(page.slots):
                spk = slot_pks.get((pid, i), "?") if self.db else "?"
                col = colors_slot[i % len(colors_slot)]
                tk.Label(inner,
                         text=f"  Slot {i}:  offset={off}  "
                              f"len={ln}B  →  registro PK={spk}",
                         bg=DARK, fg=col, font=("Consolas",10),
                         anchor="w").pack(fill="x", padx=20, pady=1)
            sep()

            # Registros en esta página — usando Text widget para scroll horizontal
            rlbl("REGISTROS EN ESTA PÁGINA:", fg=MUTED,
                 font=("Consolas",9,"bold"))
            rec_txt = tk.Text(inner, bg=DARK, fg=TEXT,
                              font=("Consolas",9),
                              wrap="none",          # sin wrap → scroll horizontal
                              relief="flat",
                              height=min(12, len(pks) * 3 + 2),
                              borderwidth=0)
            rec_hsb = tk.Scrollbar(inner, orient="horizontal",
                                   command=rec_txt.xview)
            rec_txt.configure(xscrollcommand=rec_hsb.set)
            rec_txt.pack(fill="x", padx=20, pady=(2,0))
            rec_hsb.pack(fill="x", padx=20, pady=(0,4))

            for pk in pks:
                meta = self.db._records.get(pk) if self.db else None
                if meta:
                    rec  = meta["record"]
                    line = "PK={}:  {}\n".format(
                        pk, "  |  ".join(f"{k}={v}" for k, v in rec.items()))
                    rec_txt.insert("end", line)
            rec_txt.configure(state="disabled")

        sep()
        tk.Button(inner, text="Cerrar", command=pop.destroy,
                  bg="#1a2d40", fg=TEXT, font=("Consolas",10),
                  relief="flat", padx=16, pady=6).pack(pady=(0,14))

    # ──────────────────────────────────────────────────────────────────────────
    #  DIBUJO: ÁRBOL AVL
    # ──────────────────────────────────────────────────────────────────────────

    # Máximo de nodos a dibujar en el AVL antes de colapsar la UI
    AVL_DRAW_LIMIT = 300

    def _draw_avl(self):
        c = self._avl_canvas
        c.delete("all")
        if not self.db: return

        col = self._col_var.get()
        if col.startswith("—") or col not in self.db.indices:
            return

        avl    = self.db.indices[col]
        levels = avl.bfs()
        if not levels: return

        W = c.winfo_width(); H = c.winfo_height()
        if W < 10: W = 600
        NR = 18; VG = 52
        hl = self._highlighted_pks
        pk_col = self.db.pk_column

        # ── Límite de nodos: con muchos registros dibujar congela la UI ──
        total_nodes = sum(len(lvl) for lvl in levels)
        if total_nodes > self.AVL_DRAW_LIMIT:
            # Mostrar solo estadísticas + los nodos del path de búsqueda
            c.create_text(W//2, H//2 - 24,
                          text=f"Árbol AVL — {total_nodes} nodos",
                          fill=ACCENT2, font=("Consolas",13,"bold"),
                          anchor="center")
            c.create_text(W//2, H//2 + 4,
                          text=f"Demasiados nodos para dibujar (límite: {self.AVL_DRAW_LIMIT})",
                          fill=MUTED, font=("Consolas",10), anchor="center")
            c.create_text(W//2, H//2 + 26,
                          text=f"Altura: {avl._h(avl.root)}  |  "
                               f"Nodos únicos: {avl.size}  |  "
                               f"Col: {col}",
                          fill=ACCENT, font=("Consolas",9), anchor="center")
            # si hay resultado de búsqueda, mostrarlo textualmente
            if hl:
                c.create_text(W//2, H//2 + 50,
                              text=f"Resultado encontrado: {sorted(hl)}",
                              fill=YELLOW, font=("Consolas",9,"bold"),
                              anchor="center")
            return

        pos: dict[int,tuple] = {}
        for li, level in enumerate(levels):
            n  = len(level)
            xs = [W*(i+1)/(n+1) for i in range(n)]
            y  = 28 + li*VG
            for i, nd in enumerate(level):
                pos[nd["id"]] = (xs[i], y)

        for level in levels:
            for nd in level:
                if nd["pid"] is not None and nd["pid"] in pos:
                    px,py = pos[nd["pid"]]; cx,cy = pos[nd["id"]]
                    c.create_line(px,py,cx,cy, fill=BORDER, width=1)
                    c.create_text((px+cx)/2+4,(py+cy)/2,
                                  text=nd["side"], fill=MUTED,
                                  font=("Consolas",7))

        for level in levels:
            for nd in level:
                x, y  = pos[nd["id"]]
                bf     = nd["bf"]
                bf_col = GREEN if bf==0 else YELLOW if abs(bf)==1 else RED

                # resaltar si algún PK asociado está en resultados
                if col == pk_col:
                    node_hi = nd["key"] in hl
                else:
                    node_hi = bool(set(nd.get("values_preview", [])) & hl)
                    # fallback: check via avl search
                    if not node_hi:
                        found_pks = avl.search(nd["key"])
                        node_hi   = bool(set(found_pks) & hl)

                c.create_oval(x-NR,y-NR,x+NR,y+NR,
                              fill=YELLOW_H if node_hi else ACCENT2_D,
                              outline=YELLOW if node_hi else ACCENT2_B,
                              width=2)
                # truncar key larga para que quepa en el nodo
                key_str = str(nd["key"])
                if len(key_str) > 8:
                    key_str = key_str[:7] + "…"
                c.create_text(x, y-5, text=key_str,
                              fill=YELLOW if node_hi else TEXT,
                              font=("Consolas",9,"bold"))
                c.create_text(x, y+7, text=f"bf={bf:+d}",
                              fill=bf_col, font=("Consolas",7))

        is_pk = col == pk_col
        c.create_text(8, H-14, anchor="nw",
                      text=f"AVL [{col}]  {'(PK — primario)' if is_pk else '(secundario)'}  |  "
                           f"nodos únicos: {avl.size}  |  altura: {avl._h(avl.root)}",
                      fill=MUTED, font=("Consolas",8))


# ══════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    app = App()
    app.mainloop()
    # al cerrar la ventana, flush y cerrar el archivo de disco
    if app.disk:
        app.disk.close()