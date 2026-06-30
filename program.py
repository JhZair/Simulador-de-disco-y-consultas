import csv
import io
import re
import struct
import tkinter as tk
from tkinter import filedialog, messagebox
from dataclasses import dataclass, field
from typing import Any, Optional

import customtkinter as ctk

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

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


PAGE_HDR_FMT  = ">iHH"
PAGE_HDR_SIZE = struct.calcsize(PAGE_HDR_FMT)

SLOT_FMT  = ">HH"
SLOT_SIZE = struct.calcsize(SLOT_FMT)

NO_PAGE = -1

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
    def usable_bytes(self):
        return self.sector_size_bytes - PAGE_HDR_SIZE

@dataclass
class DiskAddress:
    platter: int
    surface: int
    track:   int
    sector:  int

    def __str__(self):
        return (f"Plato {self.platter} | Sup {self.surface} | "
                f"Pista {self.track:03d} | Sector {self.sector:03d}")

class SlottedPage:

    def __init__(self, page_size: int):
        self.page_size  = page_size
        self.data       = bytearray(page_size)
        self.next_page  = NO_PAGE
        self.free_ptr   = PAGE_HDR_SIZE
        self.slots:     list[tuple[int,int]] = []

    @property
    def free_space(self) -> int:
        slot_dir_start = self.page_size - len(self.slots) * SLOT_SIZE
        return max(0, slot_dir_start - self.free_ptr - SLOT_SIZE)

    @property
    def occupancy_pct(self) -> float:
        used = (self.free_ptr - PAGE_HDR_SIZE) + len(self.slots) * SLOT_SIZE
        cap  = self.page_size - PAGE_HDR_SIZE
        return round(min(used / cap * 100, 100.0), 1) if cap > 0 else 0.0

    @property
    def slot_count(self) -> int:
        return len(self.slots)

    def insert(self, fragment: bytes) -> Optional[int]:
        if len(fragment) > self.free_space:
            return None
        offset = self.free_ptr
        self.data[offset:offset + len(fragment)] = fragment
        self.free_ptr += len(fragment)
        self.slots.append((offset, len(fragment)))
        return len(self.slots) - 1

    def delete(self, slot_idx: int) -> bool:
        if slot_idx >= len(self.slots):
            return False
        offset, length = self.slots[slot_idx]
        if slot_idx == len(self.slots) - 1:
            self.free_ptr = offset
            self.slots.pop()
            self.data[offset:offset + length] = bytes(length)
            return True
        else:
            self.slots[slot_idx] = (offset, 0)
            return False

    def read(self, slot_idx: int) -> bytes:
        if slot_idx >= len(self.slots):
            return b""
        offset, length = self.slots[slot_idx]
        return bytes(self.data[offset:offset + length])

class Disk:

    def __init__(self, config: DiskConfig):
        self.config       = config
        self._pages:      dict[int, SlottedPage] = {}
        self._current_pid = 0
        self._next_pid    = 0
        self._allocate_page()

    def _allocate_page(self) -> int:
        if self._next_pid >= self.config.total_sectors:
            raise OverflowError("Disco lleno")
        pid = self._next_pid
        self._pages[pid] = SlottedPage(self.config.sector_size_bytes)
        self._next_pid += 1
        return pid

    def _current_page(self) -> SlottedPage:
        return self._pages[self._current_pid]

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

    def write_record(self, data: bytes) -> list[tuple[int, int]]:
        fragments: list[tuple[int, int]] = []
        pid_snapshot      = self._current_pid
        next_pid_snapshot = self._next_pid
        pos = 0

        try:
            while pos < len(data):
                page = self._current_page()

                avail = page.free_space
                if avail <= 0:
                    new_pid = self._allocate_page()
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
            for frag_pid, frag_slot in fragments:
                page = self._pages.get(frag_pid)
                if page is not None:
                    page.delete(frag_slot)
            for pid_to_remove in range(next_pid_snapshot, self._next_pid):
                self._pages.pop(pid_to_remove, None)
            self._current_pid = pid_snapshot
            self._next_pid    = next_pid_snapshot
            if pid_snapshot in self._pages:
                self._pages[pid_snapshot].next_page = NO_PAGE
            raise

        return fragments

    def read_record(self, fragments: list[tuple[int, int]]) -> bytes:
        parts = []
        for pid, slot_idx in fragments:
            page = self._pages.get(pid)
            if page is None:
                raise RuntimeError(
                    f"Corrupción detectada: el fragmento apunta a la página "
                    f"{pid} que no existe en el disco. "
                    f"El índice puede estar desincronizado."
                )
            parts.append(page.read(slot_idx))
        return b"".join(parts)

    def get_page(self, pid: int) -> Optional[SlottedPage]:
        return self._pages.get(pid)

    def pages_used(self) -> int:
        return self._next_pid

class AVLNode:
    __slots__ = ("key", "values", "left", "right", "height")

    def __init__(self, key, value):
        self.key    = key
        self.values = [value]
        self.left   = None
        self.right  = None
        self.height = 1

class DuplicateKeyError(Exception):
    pass

class TypeViolation(Exception):
    pass

class AVL:

    def __init__(self, unique: bool = False):
        self.root:   Optional[AVLNode] = None
        self.size:   int  = 0
        self.unique: bool = unique

    def _height(self, n) -> int:
        return n.height if n else 0

    def _balance_factor(self, n) -> int:
        return self._height(n.left) - self._height(n.right)

    def _update_height(self, n):
        n.height = 1 + max(self._height(n.left), self._height(n.right))

    def _rotate_right(self, y):
        x = y.left; y.left = x.right; x.right = y
        self._update_height(y); self._update_height(x); return x

    def _rotate_left(self, x):
        y = x.right; x.right = y.left; y.left = x
        self._update_height(x); self._update_height(y); return y

    def _balance(self, n):
        self._update_height(n)
        bf = self._balance_factor(n)
        if bf > 1:
            if self._balance_factor(n.left) < 0:
                n.left = self._rotate_left(n.left)
            return self._rotate_right(n)
        if bf < -1:
            if self._balance_factor(n.right) > 0:
                n.right = self._rotate_right(n.right)
            return self._rotate_left(n)
        return n

    def _insert(self, node, key, value) -> tuple:
        if node is None:
            return AVLNode(key, value), True
        if key == node.key:
            if self.unique:
                raise DuplicateKeyError(
                    f"ERROR: violación de restricción de unicidad — "
                    f"la clave duplicada '{key}' viola la restricción PRIMARY KEY"
                )
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
            self.size += 1

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
                level.append({"key": node.key, "bf": self._balance_factor(node),
                              "h": node.height, "id": nid,
                              "pid": pid, "side": side})
                if node.left:  next_q.append((node.left,  nid*2+1, nid, "L"))
                if node.right: next_q.append((node.right, nid*2+2, nid, "R"))
            levels.append(level); queue = next_q
        return levels


_BOOL_TRUE_TOKENS:  set[str] = {"true", "t", "sí", "si", "verdadero", "yes", "y"}
_BOOL_FALSE_TOKENS: set[str] = {"false", "f", "no", "falso", "n"}


@dataclass
class ColumnDef:
    name:        str
    sql_type:    str
    is_pk:       bool = False
    not_null:    bool = False
    is_unique:   bool = False
    py_type:     type = str
    char_length: int  = 0

    def cast(self, v: Any) -> Any:
        is_empty = v is None or (isinstance(v, str) and v.strip() == "")
        if is_empty:
            if self.py_type is int:   return 0
            if self.py_type is float: return 0.0
            return " " * self.char_length if self.char_length > 0 else ""

        if self.py_type is int:
            if isinstance(v, str):
                low = v.strip().lower()
                if low in _BOOL_TRUE_TOKENS:
                    return 1
                if low in _BOOL_FALSE_TOKENS:
                    return 0
            try:
                f = float(v)
            except (ValueError, TypeError):
                raise TypeViolation(
                    f"el valor '{v}' no es válido para la columna "
                    f"'{self.name}' (tipo {self.sql_type})"
                )
            return int(f)

        if self.py_type is float:
            try:
                return float(v)
            except (ValueError, TypeError):
                raise TypeViolation(
                    f"el valor '{v}' no es válido para la columna "
                    f"'{self.name}' (tipo {self.sql_type})"
                )

        s = str(v)
        if self.char_length > 0:
            return s[:self.char_length].ljust(self.char_length)
        return s.strip()

@dataclass
class TableSchema:
    name:    str
    columns: list
    unique_groups: list = field(default_factory=list)

    @property
    def pk_columns(self) -> list[str]:
        pks = [c.name for c in self.columns if c.is_pk]
        if pks:
            return pks
        return [self.columns[0].name] if self.columns else []

    @property
    def is_composite_pk(self) -> bool:
        return len(self.pk_columns) > 1

    @property
    def pk_column(self) -> Optional[str]:
        cols = self.pk_columns
        return cols[0] if cols else None

    @property
    def pk_label(self) -> str:
        cols = self.pk_columns
        if len(cols) > 1:
            return "(" + ", ".join(cols) + ")"
        return cols[0] if cols else "—"

    def pk_value(self, row: dict):
        cols = self.pk_columns
        if len(cols) > 1:
            return tuple(row.get(c, "") for c in cols)
        return row.get(cols[0], "") if cols else None

    def format_pk(self, pk_val) -> str:
        if isinstance(pk_val, tuple):
            return "(" + ", ".join(str(v) for v in pk_val) + ")"
        return str(pk_val)

    def cast_row(self, row: dict) -> dict:
        cm = {c.name: c for c in self.columns}
        return {k: cm[k].cast(v) if k in cm else v for k, v in row.items()}


_INT_TYPES: set[str] = {
    "INT", "INTEGER", "SMALLINT", "BIGINT", "TINYINT",
    "MEDIUMINT", "INT1", "INT2", "INT3", "INT4", "INT8",
    "UNSIGNED", "SIGNED",
    "SERIAL", "SMALLSERIAL", "BIGSERIAL",
    "OID", "XID", "CID",
    "BIT",
    "ROWID",
    "BOOL", "BOOLEAN",
    "YEAR",
    "COUNTER",
}

_FLOAT_TYPES: set[str] = {
    "FLOAT", "REAL", "DOUBLE", "NUMERIC", "DECIMAL", "DEC",
    "DOUBLE PRECISION", "FIXED",
    "FLOAT4", "FLOAT8", "MONEY",
    "SMALLMONEY",
    "BINARY_FLOAT", "BINARY_DOUBLE",
    "NUMBER", "DECFLOAT",
    "CURRENCY",
}


def _sql_to_py(raw_type: str) -> type:
    raw   = raw_type.strip()
    upper = raw.upper()

    if re.match(r"DOUBLE\s+PRECISION", upper):
        return float

    m = re.match(r"([A-Z_ ]+?)(?:\(([^)]*)\))?$", upper.strip())
    base   = m.group(1).strip() if m else upper
    params = m.group(2)         if m else None

    if base in ("NUMBER", "DECFLOAT"):
        if params:
            parts = [p.strip() for p in params.split(",")]
            if len(parts) == 2:
                try:
                    return int if int(parts[1]) == 0 else float
                except ValueError:
                    pass
            return int
        return float

    if base in _INT_TYPES:   return int
    if base in _FLOAT_TYPES: return float
    return str


_INT_PACK_FMT  = ">i"
_INT_PACK_SIZE = struct.calcsize(_INT_PACK_FMT)
_FLT_PACK_FMT  = ">d"
_FLT_PACK_SIZE = struct.calcsize(_FLT_PACK_FMT)
_STR_LEN_FMT   = ">H"
_STR_LEN_SIZE  = struct.calcsize(_STR_LEN_FMT)
_STR_MAX_BYTES = 65535


def _serialize_record(schema: "TableSchema", row: dict) -> bytes:
    out = bytearray()
    for col in schema.columns:
        val = row.get(col.name)
        if col.py_type is int:
            ival = 0 if val is None else int(val)
            ival = max(-2_147_483_648, min(2_147_483_647, ival))
            out += struct.pack(_INT_PACK_FMT, ival)
        elif col.py_type is float:
            fval = 0.0 if val is None else float(val)
            out += struct.pack(_FLT_PACK_FMT, fval)
        elif col.char_length > 0:
            sval  = "" if val is None else str(val)
            fixed = sval[:col.char_length].ljust(col.char_length)
            out  += fixed.encode("utf-8")[:col.char_length]
        else:
            sval   = "" if val is None else str(val)
            sbytes = sval.encode("utf-8")[:_STR_MAX_BYTES]
            out   += struct.pack(_STR_LEN_FMT, len(sbytes))
            out   += sbytes
    return bytes(out)


def _deserialize_record(schema: "TableSchema", data: bytes) -> dict:
    pos = 0
    row = {}
    for col in schema.columns:
        if col.py_type is int:
            if pos + _INT_PACK_SIZE > len(data):
                break
            (ival,) = struct.unpack_from(_INT_PACK_FMT, data, pos)
            pos += _INT_PACK_SIZE
            row[col.name] = ival
        elif col.py_type is float:
            if pos + _FLT_PACK_SIZE > len(data):
                break
            (fval,) = struct.unpack_from(_FLT_PACK_FMT, data, pos)
            pos += _FLT_PACK_SIZE
            row[col.name] = fval
        elif col.char_length > 0:
            n = col.char_length
            if pos + n > len(data):
                break
            row[col.name] = data[pos:pos + n].decode("utf-8", errors="replace")
            pos += n
        else:
            if pos + _STR_LEN_SIZE > len(data):
                break
            (slen,) = struct.unpack_from(_STR_LEN_FMT, data, pos)
            pos += _STR_LEN_SIZE
            if pos + slen > len(data):
                break
            row[col.name] = data[pos:pos + slen].decode("utf-8", errors="replace")
            pos += slen
    return row


def parse_schema(text: str) -> TableSchema:
    text = text.replace("\r\n", "\n").replace("\r", "\n")

    clean = re.sub(r'/\*.*?\*/', ' ', text, flags=re.DOTALL)
    clean = re.sub(r'--[^\n]*', ' ', clean)
    clean = re.sub(r'#[^\n]*',  ' ', clean)
    clean = " ".join(clean.split())

    _QI = r'(?:[`"\[]?)(\w+)(?:[`"\]]?)'
    _PREFIX = rf'(?:{_QI}\.)*'

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
    name = m.group(m.lastindex)

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

    parts: list[str] = []
    depth    = 0
    in_str   = None
    buf      = []
    i_body   = 0
    while i_body < len(body):
        ch = body[i_body]
        if in_str:
            buf.append(ch)
            if ch == in_str:
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

    _TABLE_CONSTRAINTS = re.compile(
        r"^(?:PRIMARY\s+KEY|FOREIGN\s+KEY|UNIQUE\s+(?:KEY|INDEX)?|"
        r"UNIQUE$|CHECK\s*\(|CONSTRAINT\s+(?:\w|[`\"\[\'])|INDEX\s+|KEY\s+|"
        r"FULLTEXT|SPATIAL|CLUSTERED|NONCLUSTERED)",
        re.IGNORECASE
    )

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
        r"VISIBLE|INVISIBLE|"
        r"PRIMARY\s+KEY"
        r")\b",
        re.IGNORECASE
    )

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

    cols:           list[ColumnDef] = []
    pk_columns:     list[str]       = []
    pk_warnings:    list[str]       = []
    unique_groups:  list[list[str]] = []

    for part in parts:
        part = part.strip()
        if not part:
            continue

        upper_part = part.upper().lstrip()

        if _TABLE_CONSTRAINTS.match(upper_part):
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
                        f"PK compuesta detectada {found_pks} — se usará la "
                        f"combinación de estas {len(found_pks)} columnas "
                        f"como clave primaria única (no solo la primera)."
                    )
            else:
                uniq_m = re.search(
                    r"UNIQUE\s*(?:KEY\s+\S+\s*|INDEX\s+\S+\s*)?\(([^)]+)\)",
                    part, re.IGNORECASE)
                if uniq_m:
                    found_uniq = [
                        k.strip().strip("`\"[]'")
                        for k in uniq_m.group(1).split(",")
                    ]
                    unique_groups.append(found_uniq)
            continue

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
            cols.append(ColumnDef(
                name=cname, sql_type="VARCHAR",
                py_type=str, is_pk=False, not_null=False
            ))
            continue

        is_pk = bool(re.search(r"\bPRIMARY\s+KEY\b", rest, re.IGNORECASE))
        if is_pk:
            pk_columns.append(cname)

        is_unique_inline = (not is_pk) and bool(
            re.search(r"\bUNIQUE\b", rest, re.IGNORECASE))

        rest_for_type = re.sub(r"^PRIMARY\s+KEY\s*", "", rest.strip(), flags=re.IGNORECASE).strip()
        rest_for_type = _INLINE_STRIP.sub(" ", rest_for_type).strip()
        if not rest_for_type:
            raw_type = "VARCHAR"
        else:
            two = _TWO_WORD_TYPES.match(rest_for_type)
            if two:
                raw_type = two.group(0).strip()
            else:
                type_m = re.match(
                    r"([`\w]+(?:\s*\([^)]*\))?)",
                    rest_for_type
                )
                raw_type = (type_m.group(1).strip().strip("`")
                            if type_m else "VARCHAR")

        raw_type_clean = re.sub(r'\s+', ' ', raw_type).strip()

        not_null = is_pk or bool(
            re.search(r"\bNOT\s+NULL\b", rest, re.IGNORECASE))

        cols.append(ColumnDef(
            name      = cname,
            sql_type  = raw_type_clean,
            is_pk     = is_pk,
            not_null  = not_null,
            is_unique = is_unique_inline,
            py_type   = _sql_to_py(raw_type_clean),
        ))

    pk_set = set(pk_columns)
    for c in cols:
        if c.name in pk_set:
            c.is_pk    = True
            c.not_null = True
            c.is_unique = False

    if not any(c.is_pk for c in cols) and cols:
        cols[0].is_pk    = True
        cols[0].not_null = True

    for c in cols:
        if c.is_unique:
            unique_groups.append([c.name])

    pk_cols_final = [c.name for c in cols if c.is_pk] or \
                    ([cols[0].name] if cols else [])
    unique_groups = [
        g for g in unique_groups
        if sorted(g) != sorted(pk_cols_final)
    ]

    if not cols:
        raise ValueError(
            "No se encontraron columnas válidas en el CREATE TABLE.\n"
            "Verifica que el archivo sea un CREATE TABLE estándar SQL."
        )

    schema = TableSchema(name, cols, unique_groups=unique_groups)
    schema._pk_warnings = pk_warnings
    return schema



class DatabaseManager:

    def __init__(self, disk: Disk):
        self.disk                    = disk
        self.indices: dict[str, AVL] = {}
        self.schema: Optional[TableSchema] = None
        self.records_loaded          = 0
        self._records: dict          = {}
        self._unique_seen: dict      = {}

    def load_schema(self, path: str) -> list[str]:
        encoding = self._detect_encoding(path)
        with open(path, encoding=encoding, errors="replace") as f:
            self.schema = parse_schema(f.read())
        return getattr(self.schema, "_pk_warnings", [])

    @staticmethod
    def _detect_encoding(path: str) -> str:
        with open(path, "rb") as f:
            raw = f.read(8192)

        if raw.startswith(b"\xff\xfe\x00\x00") or raw.startswith(b"\x00\x00\xfe\xff"):
            return "utf-32"
        if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
            return "utf-16"
        if raw.startswith(b"\xef\xbb\xbf"):
            return "utf-8-sig"

        try:
            raw.decode("utf-8")
            return "utf-8"
        except UnicodeDecodeError:
            pass

        for enc in ("cp1252", "iso-8859-1", "latin-1"):
            try:
                raw.decode(enc)
                return enc
            except UnicodeDecodeError:
                continue

        return "latin-1"

    @staticmethod
    def _detect_delimiter(path: str, encoding: str) -> str:
        candidates = [",", ";", "\t", "|", ":"]
        try:
            with open(path, encoding=encoding, errors="replace") as f:
                lines = [f.readline() for _ in range(5)]
            lines = [l for l in lines if l.strip()]
            if not lines:
                return ","

            scores: dict[str, list[int]] = {d: [] for d in candidates}
            for line in lines:
                for d in candidates:
                    scores[d].append(line.count(d))

            best_delim = ","
            best_score = -1
            for d in candidates:
                counts = scores[d]
                if not counts or max(counts) == 0:
                    continue
                avg = sum(counts) / len(counts)
                variance = sum((c - avg) ** 2 for c in counts) / len(counts)
                score = avg - variance * 0.1
                if score > best_score:
                    best_score = score
                    best_delim = d

            return best_delim
        except Exception:
            return ","

    def load_csv(self, path: str) -> list[str]:
        if not self.schema:
            raise RuntimeError("Carga el esquema primero")

        warnings: list[str] = []
        encoding = self._detect_encoding(path)
        delimiter = self._detect_delimiter(path, encoding)

        with open(path, newline="", encoding=encoding, errors="replace") as f:
            sample = f.read(3)
            if sample.startswith("\ufeff"):
                sample = sample[1:]
            else:
                f.seek(0)
                sample = ""
            content = sample + f.read()

        reader_f   = io.StringIO(content)
        first_row  = next(csv.reader(reader_f, delimiter=delimiter), [])
        schema_names = [c.name for c in self.schema.columns]

        def _normalise(s: str) -> str:
            return s.strip().lstrip("\ufeff").lower()

        first_row_norm   = [_normalise(f) for f in first_row]
        schema_names_norm = [_normalise(n) for n in schema_names]

        if schema_names_norm and first_row_norm:
            schema_set  = set(schema_names_norm)
            matches     = sum(1 for f in first_row_norm if f in schema_set)
            has_header  = matches >= max(1, len(schema_names_norm) // 2)
        else:
            has_header = False

        reader_f.seek(0)

        if has_header:
            reader     = csv.DictReader(reader_f, delimiter=delimiter)
            fieldnames = [_normalise(f) for f in (reader.fieldnames or [])]
            reader_f.seek(0)
            reader_f.readline()
            reader = csv.DictReader(reader_f,
                                    fieldnames=fieldnames,
                                    delimiter=delimiter)
        else:
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

        pk_cols          = self.schema.pk_columns
        pk_set           = set(pk_cols)
        dup_pks: int     = 0
        notnull_viol: int = 0
        unique_viol: int  = 0
        type_viol: int    = 0
        err_rows: int    = 0

        for line_num, raw_row in enumerate(reader, start=2):
            row = {
                k.strip().lstrip("\ufeff"): v
                for k, v in (raw_row or {}).items()
                if k is not None
            }

            if not any(v and str(v).strip() for v in row.values()):
                continue

            try:
                for col in self.schema.columns:
                    if col.name not in row:
                        row[col.name] = ""

                raw_pk_parts = [row.get(c, "") for c in pk_cols]
                raw_pk_empty = all(
                    p is None or str(p).strip() == "" for p in raw_pk_parts
                )

                null_col = next(
                    (c.name for c in self.schema.columns
                     if c.not_null and c.name not in pk_set
                     and (row.get(c.name) is None
                          or str(row.get(c.name)).strip() == "")),
                    None
                )
                if null_col:
                    notnull_viol += 1
                    if notnull_viol <= 5:
                        warnings.append(
                            f"Fila {line_num}: ERROR — violación de restricción "
                            f"NOT NULL: la columna '{null_col}' no puede estar "
                            f"vacía — INSERT rechazado."
                        )
                    continue

                try:
                    casted = self.schema.cast_row(row)
                except TypeViolation as tv:
                    type_viol += 1
                    if type_viol <= 5:
                        warnings.append(
                            f"Fila {line_num}: ERROR — tipo de dato inválido: "
                            f"{tv} — INSERT rechazado."
                        )
                    continue
                casted = {k: v for k, v in casted.items() if k in schema_cols}

                if raw_pk_empty:
                    auto_val = f"__auto_{self.records_loaded}"
                    casted[pk_cols[0]] = auto_val
                    pk_val = self.schema.pk_value(casted)
                    if self.records_loaded < 5:
                        warnings.append(
                            f"Fila {line_num}: PK vacía — asignada clave "
                            f"automática '{auto_val}'."
                        )
                else:
                    pk_val = self.schema.pk_value(casted)

                if pk_val in self._records:
                    dup_pks += 1
                    if dup_pks <= 5:
                        warnings.append(
                            f"Fila {line_num}: ERROR — violación de restricción "
                            f"PRIMARY KEY: la clave duplicada "
                            f"{self.schema.format_pk(pk_val)} ya existe "
                            f"— INSERT rechazado."
                        )
                    continue

                uniq_hit = None
                for group in self.schema.unique_groups:
                    gkey = tuple(group)
                    val  = tuple(casted.get(c, "") for c in group)
                    seen = self._unique_seen.get(gkey, set())
                    if val in seen:
                        uniq_hit = (group, val)
                        break
                if uniq_hit:
                    group, val = uniq_hit
                    unique_viol += 1
                    if unique_viol <= 5:
                        label = group[0] if len(group) == 1 else \
                                "(" + ", ".join(group) + ")"
                        vdisp = val[0] if len(val) == 1 else \
                                "(" + ", ".join(str(v) for v in val) + ")"
                        warnings.append(
                            f"Fila {line_num}: ERROR — violación de restricción "
                            f"UNIQUE en {label}: el valor {vdisp} ya existe "
                            f"— INSERT rechazado."
                        )
                    continue

                for group in self.schema.unique_groups:
                    gkey = tuple(group)
                    val  = tuple(casted.get(c, "") for c in group)
                    self._unique_seen.setdefault(gkey, set()).add(val)

                self._store(casted)
                self.records_loaded += 1

            except OverflowError:
                warnings.append(
                    f"Fila {line_num}: DISCO LLENO — carga interrumpida. "
                    f"Se cargaron {self.records_loaded} registro(s) correctamente "
                    f"antes de agotar el espacio disponible."
                )
                break

            except Exception as exc:
                err_rows += 1
                if err_rows <= 5:
                    warnings.append(
                        f"Fila {line_num}: error ({exc}) — omitida."
                    )

        if dup_pks > 5:
            warnings.append(f"… y {dup_pks - 5} violación(es) de PRIMARY KEY más — INSERT rechazado.")
        if notnull_viol > 5:
            warnings.append(f"… y {notnull_viol - 5} violación(es) de NOT NULL más — INSERT rechazado.")
        if unique_viol > 5:
            warnings.append(f"… y {unique_viol - 5} violación(es) de UNIQUE más — INSERT rechazado.")
        if type_viol > 5:
            warnings.append(f"… y {type_viol - 5} fila(s) con tipo de dato inválido más — INSERT rechazado.")
        if err_rows > 5:
            warnings.append(f"… y {err_rows - 5} fila(s) con error más omitidas.")

        self.indices.clear()

        if hasattr(self.schema, "_pk_warnings"):
            warnings = self.schema._pk_warnings + warnings

        return warnings

    def _store(self, row: dict):
        raw       = _serialize_record(self.schema, row)
        pk_val    = self.schema.pk_value(row)
        fragments = self.disk.write_record(raw)
        self._records[pk_val] = {
            "record":    row,
            "fragments": fragments,
            "raw_len":   len(raw),
        }


    def _build_index(self, col: str) -> AVL:
        if col in self.indices:
            return self.indices[col]

        pk_col = self.schema.pk_column
        is_pk  = (col == pk_col) and not self.schema.is_composite_pk
        avl    = AVL(unique=is_pk)

        for pk_val, meta in self._records.items():
            if is_pk:
                avl.insert(pk_val, meta["fragments"])
            else:
                attr_val = meta["record"].get(col, "")
                avl.insert(attr_val, pk_val)

        self.indices[col] = avl
        return avl

    def index_exists(self, col: str) -> bool:
        return col in self.indices

    def _fetch_by_pk(self, pk_val) -> Optional[dict]:
        meta = self._records.get(pk_val)
        if meta is None:
            return None
        frags  = meta["fragments"]
        raw    = self.disk.read_record(frags)
        record = _deserialize_record(self.schema, raw)
        if not record:
            record = {"_raw_hex": raw.hex()}

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


    def _cast_for_col(self, col: str, value: str) -> Any:
        col_def = next((c for c in self.schema.columns
                        if c.name == col), None)
        if col_def:
            return col_def.cast(value)
        return value

    def search(self, col: str, value: str) -> list[dict]:
        if not self.schema or col not in self.columns:
            return []
        pk_col  = self.schema.pk_column
        is_simple_pk_col = (col == pk_col) and not self.schema.is_composite_pk
        coerced = self._cast_for_col(col, value)
        avl     = self._build_index(col)
        values  = avl.search(coerced)
        if not values:
            return []

        if is_simple_pk_col:
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
        if not self.schema or col not in self.columns:
            return []
        pk_col = self.schema.pk_column
        is_simple_pk_col = (col == pk_col) and not self.schema.is_composite_pk
        lo_v   = self._cast_for_col(col, lo)
        hi_v   = self._cast_for_col(col, hi)
        avl    = self._build_index(col)
        hits   = avl.range_search(lo_v, hi_v)

        out = []; seen = set()
        for key, values in hits:
            if is_simple_pk_col:
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

        r = self._section(left, r, "(1) GEOMETRÍA DEL DISCO",
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
                  f"   Header fijo: {PAGE_HDR_SIZE}B | Slot: {SLOT_SIZE}B c/u\n"
                  f"   Registros: binario puro (INT=4B, FLOAT=8B,\n"
                  f"   VARCHAR=2B+datos). Sin nombres de columna en disco."),
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

        r = self._section(left, r, "(2) ESQUEMA (.txt) Y DATOS (.csv)",
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

        r = self._section(left, r, "(3) BÚSQUEDA",
                          GREEN, GREEN_D, GREEN_H)

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

        r = self._section(left, r, "LOG DEL SISTEMA", MUTED, MUTED_D, BORDER)

        self._log_box = ctk.CTkTextbox(left, height=110, font=FMS,
                                       fg_color=DARK, text_color=MUTED,
                                       border_color=BORDER, border_width=1)
        self._log_box.grid(row=r, column=0, sticky="ew", pady=(0,8)); r+=1

        ctk.CTkButton(left, text="Reiniciar",
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
                self._result_box.insert(
                    "end",
                    f"  [Tamaño en disco: {item['raw_len']} B binarios]\n")
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

    def _cmd_configure(self):
        try:
            cfg = DiskConfig(self._vp.get(), self._vt.get(),
                             self._vs.get(), self._vb.get())
            if cfg.platters <= 0 or cfg.tracks_per_surface <= 0 \
               or cfg.sectors_per_track <= 0:
                messagebox.showerror("Error",
                    "La geometría del disco debe tener al menos 1 plato, "
                    "1 pista por superficie y 1 sector por pista.")
                return
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
            self.disk = Disk(self.disk.config)
            self.db   = DatabaseManager(self.disk)
            schema_warnings = self.db.load_schema(self._txt_path)
            sch = self.db.schema
            cols_txt = "  ".join(
                f"{'[PK]' if c.is_pk else ''}{c.name}:{c.py_type.__name__}"
                for c in sch.columns)
            self._schema_lbl.configure(
                text=f"Tabla: {sch.name}  |  PK: {sch.pk_label}\n{cols_txt}")
            n_cols = len(sch.columns)
            self._log(
                f"Esquema: '{sch.name}'  PK={sch.pk_label}  "
                f"→  {n_cols} columnas detectadas", GREEN)
            for w in schema_warnings:
                self._log(f"⚠  {w}", YELLOW)

            csv_warnings = self.db.load_csv(self._csv_path)
            all_warnings = schema_warnings + csv_warnings
            pages = self.disk.pages_used()
            self._log(f"{self.db.records_loaded} registros  ·  "
                      f"{pages} página(s) usada(s)", GREEN)

            if csv_warnings:
                for w in csv_warnings:
                    self._log(f"⚠  {w}", YELLOW)
            if all_warnings:
                messagebox.showwarning(
                    "Advertencias al cargar",
                    "\n\n".join(all_warnings)
                )
            occ_list = [self.disk.get_page(i).occupancy_pct
                        for i in range(pages)]
            avg_occ = sum(occ_list)/len(occ_list) if occ_list else 0
            self._log(f"Ocupación promedio de páginas: {avg_occ:.1f}%", ACCENT)

            self._highlighted_pks = set()
            cols = self.db.columns
            self._col_menu.configure(values=cols)
            self._col_var.set(self.db.pk_column or cols[0])
            self._draw_disk()
            self._draw_avl()
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

    def _draw_disk(self):
        c = self._disk_canvas
        c.delete("all")
        self._sector_items = {}
        if not self.disk: return

        cfg     = self.disk.config
        SW      = 16; SH = 16; SG = 2
        TRACK_H = SH + SG
        PAD     = 10; LABEL_W = 50

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
                        pid = self.disk.address_to_linear(
                            DiskAddress(pi, si, ti, seci))

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

                            bar_h   = max(2, int(SH * occ / 100))
                            bar_col = (YELLOW if hi
                                       else (GREEN if occ >= 99.9 else ORANGE))
                            c.create_rectangle(
                                x+1, y+SH-bar_h, x+SW-1, y+SH-1,
                                fill=bar_col, outline="")

                            if len(pks) > 1:
                                c.create_rectangle(
                                    x+SW-4, y, x+SW, y+4,
                                    fill=ACCENT2, outline="")

                            info = {"pid": pid, "page": page,
                                    "pks": pks, "occ": occ,
                                    "pi": pi, "si": si,
                                    "ti": ti, "seci": seci}
                        elif page:
                            item = c.create_rectangle(
                                x, y, x+SW, y+SH,
                                fill="#1a2d40", outline=BORDER, width=1)
                            info = None
                        else:
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


    def _popup_page(self, pid, pi, si, ti, seci, info):
        pop = tk.Toplevel(self)
        pop.title(f"Página {pid}  P{pi}·S{si}·T{ti:02d}·Sec{seci:02d}")
        pop.configure(bg=PANEL)
        pop.resizable(True, True)
        pop.geometry("640x560")
        pop.minsize(500, 320)
        pop.grab_set()

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

        inner = tk.Frame(_canvas, bg=PANEL)
        win_id = _canvas.create_window((0, 0), window=inner, anchor="nw")

        def _on_inner_configure(e):
            _canvas.configure(scrollregion=_canvas.bbox("all"))
        def _on_canvas_configure(e):
            _canvas.itemconfig(win_id, width=e.width)
        inner.bind("<Configure>", _on_inner_configure)
        _canvas.bind("<Configure>", _on_canvas_configure)

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

            rlbl("ESTRUCTURA DE LA PÁGINA:", fg=MUTED,
                 font=("Consolas",9,"bold"))
            BAR_W = 560
            sc = tk.Canvas(inner, width=BAR_W, height=54,
                           bg=PANEL, highlightthickness=0)
            sc.pack(padx=20, pady=4, anchor="w")

            hw = int(BAR_W * PAGE_HDR_SIZE / sz)
            sc.create_rectangle(0,6,hw,48, fill="#1a2d40", outline=ACCENT)
            sc.create_text(hw//2, 27, text=f"HDR\n{PAGE_HDR_SIZE}B",
                           fill=ACCENT, font=("Consolas",7,"bold"))

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

            free_x = hw + int(BAR_W * used / sz)
            free_w = BAR_W - free_x - int(BAR_W * page.slot_count * SLOT_SIZE / sz)
            if free_w > 0:
                sc.create_rectangle(free_x, 6, free_x+free_w, 48,
                                    fill="#1a2d40", outline=BORDER)
                if free_w > 30:
                    sc.create_text(free_x+free_w//2, 27,
                                   text=f"libre\n{free}B",
                                   fill=MUTED, font=("Consolas",7))

            sd_w = int(BAR_W * page.slot_count * SLOT_SIZE / sz)
            if sd_w > 0:
                sc.create_rectangle(BAR_W-sd_w, 6, BAR_W, 48,
                                    fill="#2a1545", outline=ACCENT2)
                if sd_w > 20:
                    sc.create_text(BAR_W-sd_w//2, 27,
                                   text=f"dir\n{page.slot_count*SLOT_SIZE}B",
                                   fill=ACCENT2, font=("Consolas",7))

            sep()

            rlbl("SLOTS:", fg=MUTED, font=("Consolas",9,"bold"))
            if self.db:
                slot_pks: dict[tuple,str] = {}
                for pk, meta in self.db._records.items():
                    for fpid, fslot in meta["fragments"]:
                        if fpid == pid:
                            slot_pks[(fpid, fslot)] = pk

            for i, (off, ln) in enumerate(page.slots):
                spk = slot_pks.get((pid, i), "?") if self.db else "?"
                spk_disp = self.db.schema.format_pk(spk) if (self.db and spk != "?") else spk
                col = colors_slot[i % len(colors_slot)]
                tk.Label(inner,
                         text=f"  Slot {i}:  offset={off}  "
                              f"len={ln}B  →  registro PK={spk_disp}",
                         bg=DARK, fg=col, font=("Consolas",10),
                         anchor="w").pack(fill="x", padx=20, pady=1)
            sep()

            rlbl("REGISTROS EN ESTA PÁGINA:", fg=MUTED,
                 font=("Consolas",9,"bold"))
            rec_txt = tk.Text(inner, bg=DARK, fg=TEXT,
                              font=("Consolas",9),
                              wrap="none",
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
                    raw_len = meta["raw_len"]
                    line = "PK={}  [{} B binarios]:  {}\n".format(
                        self.db.schema.format_pk(pk),
                        raw_len,
                        "  |  ".join(f"{k}={v}" for k, v in rec.items()))
                    rec_txt.insert("end", line)
            rec_txt.configure(state="disabled")

        sep()
        tk.Button(inner, text="Cerrar", command=pop.destroy,
                  bg="#1a2d40", fg=TEXT, font=("Consolas",10),
                  relief="flat", padx=16, pady=6).pack(pady=(0,14))

    AVL_DRAW_LIMIT = 300

    def _draw_avl(self):
        c = self._avl_canvas
        c.delete("all")
        if not self.db: return

        col = self._col_var.get()
        if col.startswith("—"):
            return

        if col not in self.db.indices:
            W = c.winfo_width(); H = c.winfo_height()
            if W < 10: W = 600
            if H < 10: H = 200
            c.create_text(W//2, H//2,
                          text=f"Índice de '{col}' aún no construido —\n"
                               f"realiza una búsqueda por esta columna "
                               f"para generarlo.",
                          fill=MUTED, font=("Consolas",10),
                          justify="center", anchor="center")
            return

        avl    = self.db.indices[col]
        levels = avl.bfs()
        if not levels: return

        W = c.winfo_width(); H = c.winfo_height()
        if W < 10: W = 600
        NR = 18; VG = 52
        hl = self._highlighted_pks
        pk_col = self.db.pk_column
        is_simple_pk_col = (col == pk_col) and not self.db.schema.is_composite_pk

        total_nodes = sum(len(lvl) for lvl in levels)
        if total_nodes > self.AVL_DRAW_LIMIT:
            c.create_text(W//2, H//2 - 24,
                          text=f"Árbol AVL — {total_nodes} nodos",
                          fill=ACCENT2, font=("Consolas",13,"bold"),
                          anchor="center")
            c.create_text(W//2, H//2 + 4,
                          text=f"Demasiados nodos para dibujar (límite: {self.AVL_DRAW_LIMIT})",
                          fill=MUTED, font=("Consolas",10), anchor="center")
            c.create_text(W//2, H//2 + 26,
                          text=f"Altura: {avl._height(avl.root)}  |  "
                               f"Nodos únicos: {avl.size}  |  "
                               f"Col: {col}",
                          fill=ACCENT, font=("Consolas",9), anchor="center")
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

                if is_simple_pk_col:
                    node_hi = nd["key"] in hl
                else:
                    found_pks = avl.search(nd["key"])
                    node_hi   = bool(set(found_pks) & hl)

                c.create_oval(x-NR,y-NR,x+NR,y+NR,
                              fill=YELLOW_H if node_hi else ACCENT2_D,
                              outline=YELLOW if node_hi else ACCENT2_B,
                              width=2)
                key_str = str(nd["key"])
                if len(key_str) > 8:
                    key_str = key_str[:7] + "…"
                c.create_text(x, y-5, text=key_str,
                              fill=YELLOW if node_hi else TEXT,
                              font=("Consolas",9,"bold"))
                c.create_text(x, y+7, text=f"bf={bf:+d}",
                              fill=bf_col, font=("Consolas",7))

        is_pk = is_simple_pk_col
        c.create_text(8, H-14, anchor="nw",
                      text=f"AVL [{col}]  {'(PK — primario)' if is_pk else '(secundario)'}  |  "
                           f"nodos únicos: {avl.size}  |  altura: {avl._height(avl.root)}",
                      fill=MUTED, font=("Consolas",8))



if __name__ == "__main__":
    app = App()
    app.mainloop()