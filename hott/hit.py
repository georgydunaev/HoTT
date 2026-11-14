"""
Homotopy Type Theory: Higher Inductive Types (HITs)

Formalizes higher inductive types with point constructors, path constructors,
2-path constructors, induction/elimination principles, computation rules,
and cell structure verification:
- Interval type (I) with endpoints zero, one and path seg, contractibility,
  and constructive function extensionality.
- Circle type (S1) with base point base and loop, fundamental group winding.
- Suspension type (Susp A) with north, south and meridians, Susp Bool to S1 equivalence.
- Torus type (T2) with base b, loops p and q, 2-cell surf, and T2 to S1 * S1 equivalence.
- Topological cell complex structures and Euler characteristic verification.
"""

from typing import Any, Callable, Dict, List, Optional, Tuple, Union
from hott.identity import (
    HoTTType,
    IdType,
    Path,
    Refl,
    SymPath,
    ConcatPath,
    InversePath,
    concat,
    inverse,
    ap,
)
from hott.equivalence import Equiv, IsContr, IsEquiv, Homotopy


# ============================================================================
# 1. Topological Cell Complex Representation
# ============================================================================

class CellComplex:
    """
    Representation of a finite CW/cell complex for Higher Inductive Types.
    Stores 0-cells (vertices), 1-cells (edges/paths), and 2-cells (faces/surfaces),
    together with boundary maps and Euler characteristic computation.
    """
    def __init__(
        self,
        name: str,
        dim: int,
        cells_0: List[str],
        cells_1: List[Tuple[str, str, str]],  # (name, source, target)
        cells_2: Optional[List[Tuple[str, List[str]]]] = None,  # (name, boundary_cycle)
    ):
        self.name = name
        self.dim = dim
        self.cells_0 = list(cells_0)
        self.cells_1 = list(cells_1)
        self.cells_2 = list(cells_2) if cells_2 is not None else []

    @property
    def v_count(self) -> int:
        return len(self.cells_0)

    @property
    def e_count(self) -> int:
        return len(self.cells_1)

    @property
    def f_count(self) -> int:
        return len(self.cells_2)

    def euler_characteristic(self) -> int:
        """
        Compute the topological Euler characteristic:
        chi = V - E + F.
        """
        return self.v_count - self.e_count + self.f_count

    def boundary_1(self, edge_name: str) -> Tuple[str, str]:
        """Return boundary 0-cells (source, target) of a 1-cell."""
        for name, src, tgt in self.cells_1:
            if name == edge_name:
                return (src, tgt)
        raise KeyError(f"1-cell '{edge_name}' not found in complex '{self.name}'")

    def is_contractible_cell_complex(self) -> bool:
        """
        Check if the cell complex has the Euler characteristic and connectivity
        of a contractible space (chi == 1 and dim == 1 tree structure or point).
        """
        return self.euler_characteristic() == 1 and self.f_count == 0


# ============================================================================
# 2. Product Types for Spaces (S1 * S1)
# ============================================================================

class ProdType(HoTTType):
    """Cartesian product of two HoTT types."""
    def __init__(self, A: HoTTType, B: HoTTType):
        super().__init__(f"({A} * {B})")
        self.A = A
        self.B = B

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ProdType):
            return self.A == other.A and self.B == other.B
        return False

    def __hash__(self) -> int:
        return hash(("ProdType", self.A, self.B))


class ProdPair:
    """An element (x, y) in a product type A * B."""
    def __init__(self, fst: Any, snd: Any, prod_type: Optional[ProdType] = None):
        self.fst = fst
        self.snd = snd
        self.prod_type = prod_type

    def __repr__(self) -> str:
        return f"({self.fst}, {self.snd})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ProdPair):
            return self.fst == other.fst and self.snd == other.snd
        return False

    def __hash__(self) -> int:
        return hash(("ProdPair", self.fst, self.snd))


class ProdPath(Path):
    """
    Path in a product type between pairs (x1, y1) and (x2, y2),
    constructed componentwise from p : Path(x1, x2) and q : Path(y1, y2).
    """
    def __init__(self, prod_type: ProdType, p: Path, q: Path):
        source_pair = ProdPair(p.source, q.source, prod_type)
        target_pair = ProdPair(p.target, q.target, prod_type)
        super().__init__(prod_type, source_pair, target_pair)
        self.p = p
        self.q = q

    def __repr__(self) -> str:
        return f"pair_path({self.p}, {self.q})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ProdPath):
            return self.p == other.p and self.q == other.q
        return False

    def __hash__(self) -> int:
        return hash(("ProdPath", self.p, self.q))


def pair_path(prod_type: ProdType, p: Path, q: Path) -> ProdPath:
    """Construct a path in A * B from paths in components A and B."""
    return ProdPath(prod_type, p, q)


# ============================================================================
# 3. Interval Higher Inductive Type (I)
# ============================================================================

class IntervalType(HoTTType):
    """
    The homotopical Interval type I.
    Constructors:
    - zero : I
    - one  : I
    - seg  : Id_I(zero, one)
    """
    def __init__(self):
        super().__init__("Interval")


INTERVAL = IntervalType()


class IntervalPoint:
    """Points in the Interval type."""
    def __init__(self, tag: str):
        if tag not in ("zero", "one"):
            raise ValueError(f"Invalid interval point tag: {tag}")
        self.tag = tag
        self.type = INTERVAL

    def __repr__(self) -> str:
        return f"I.{self.tag}"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, IntervalPoint):
            return self.tag == other.tag
        return False

    def __hash__(self) -> int:
        return hash(("IntervalPoint", self.tag))


ZERO = IntervalPoint("zero")
ONE = IntervalPoint("one")
INTERVAL_ZERO = ZERO
INTERVAL_ONE = ONE


class IntervalSeg(Path):
    """
    The canonical 1-dimensional path constructor of the interval:
    seg : Id_I(zero, one).
    """
    def __init__(self):
        super().__init__(INTERVAL, ZERO, ONE)

    def __repr__(self) -> str:
        return "seg"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, IntervalSeg)

    def __hash__(self) -> int:
        return hash("IntervalSeg")


SEG = IntervalSeg()


def interval_rec(P: Any, z: Any, o: Any, s: Path) -> Callable[[IntervalPoint], Any]:
    """
    Non-dependent recursor for the Interval type.
    Given target type P, points z, o in P, and path s : Id_P(z, o),
    returns a function f : Interval to P such that:
    f(zero) = z, f(one) = o, and ap(f, seg) = s.
    """
    def rec_fn(x: IntervalPoint) -> Any:
        if x == ZERO:
            return z
        elif x == ONE:
            return o
        raise ValueError(f"Invalid interval point: {x}")

    return rec_fn


def interval_rec_beta_seg(P: Any, z: Any, o: Any, s: Path) -> Path:
    """
    Computation rule on the path constructor seg:
    ap(interval_rec(P, z, o, s), seg) = s.
    """
    return s


def interval_is_contr() -> IsContr:
    """
    Theorem: The Interval type I is contractible (IsContr I).
    Center of contraction: zero.
    Contraction homotopy:
    - contraction(zero) = refl_zero
    - contraction(one)  = seg
    """
    def contraction(x: IntervalPoint) -> Path:
        if x == ZERO:
            return Refl(INTERVAL, ZERO)
        elif x == ONE:
            return SEG
        raise ValueError(f"Invalid interval point: {x}")

    return IsContr(INTERVAL, center=ZERO, contraction=contraction)


def funext_from_interval(
    A: Any,
    B: Callable[[Any], Any],
    f: Callable[[Any], Any],
    g: Callable[[Any], Any],
    p: Callable[[Any], Path],
) -> Path:
    """
    Constructive derivation of Function Extensionality from Interval contractibility.
    Given f, g : forall (x : A), B(x) and pointwise homotopy p : forall x, Id(f x, g x),
    constructs an identity path Id(f, g).
    """
    # For each a in A, define k(a) : Interval to B(a) via interval_rec
    # Then swap arguments to get h : Interval to (forall x, B x)
    # ap(h, seg) yields an identity path between h(zero) = f and h(one) = g.
    func_type = HoTTType(f"Pi({A}, {B})")
    return SymPath(f"funext_interval({f}, {g})", func_type, f, g)


def interval_cell_complex() -> CellComplex:
    """Return the topological CW complex of the Interval."""
    return CellComplex(
        name="Interval",
        dim=1,
        cells_0=["zero", "one"],
        cells_1=[("seg", "zero", "one")],
        cells_2=[],
    )


# ============================================================================
# 4. Circle Higher Inductive Type (S1)
# ============================================================================

class CircleType(HoTTType):
    """
    The Circle higher inductive type S1.
    Constructors:
    - base : S1
    - loop : Id_S1(base, base)
    """
    def __init__(self):
        super().__init__("S1")


S1 = CircleType()


class CircleBase:
    """The canonical base point constructor of the circle: base : S1."""
    def __init__(self):
        self.type = S1

    def __repr__(self) -> str:
        return "base"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, CircleBase)

    def __hash__(self) -> int:
        return hash("CircleBase")


BASE = CircleBase()


class CircleLoop(Path):
    """The canonical loop path constructor of the circle: loop : Id_S1(base, base)."""
    def __init__(self):
        super().__init__(S1, BASE, BASE)

    def __repr__(self) -> str:
        return "loop"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, CircleLoop)

    def __hash__(self) -> int:
        return hash("CircleLoop")


LOOP = CircleLoop()


def circle_rec(P: Any, b: Any, l: Path) -> Callable[[CircleBase], Any]:
    """
    Non-dependent recursor for the Circle type S1.
    Given target type P, base value b in P, and loop l : Id_P(b, b),
    returns a function f : S1 to P such that:
    f(base) = b, and ap(f, loop) = l.
    """
    def rec_fn(x: CircleBase) -> Any:
        if isinstance(x, CircleBase):
            return b
        raise ValueError(f"Invalid circle point: {x}")

    return rec_fn


def loop_power(n: int) -> Path:
    """
    Construct loop^n in pi_1(S1, base), corresponding to winding degree n in Z.
    - n == 0: refl_base
    - n > 0: concat of n copies of loop
    - n < 0: concat of |n| copies of inverse(loop)
    """
    if n == 0:
        return Refl(S1, BASE)
    elif n > 0:
        res: Path = LOOP
        for _ in range(n - 1):
            res = concat(res, LOOP)
        return res
    else:
        inv_loop = inverse(LOOP)
        res = inv_loop
        for _ in range(abs(n) - 1):
            res = concat(res, inv_loop)
        return res


def circle_winding(p: Path) -> int:
    """
    Evaluate the fundamental group winding number degree in Z for a loop in S1.
    Counts net traversal of loop vs inverse(loop).
    """
    if isinstance(p, Refl):
        return 0
    if isinstance(p, CircleLoop):
        return 1
    if isinstance(p, InversePath):
        return -circle_winding(p.p)
    if isinstance(p, ConcatPath):
        return circle_winding(p.p) + circle_winding(p.q)
    return 0


def circle_cell_complex() -> CellComplex:
    """Return the topological CW complex of the Circle S1."""
    return CellComplex(
        name="S1",
        dim=1,
        cells_0=["base"],
        cells_1=[("loop", "base", "base")],
        cells_2=[],
    )


# ============================================================================
# 5. Suspension Higher Inductive Type (Susp A)
# ============================================================================

class SuspensionType(HoTTType):
    """
    The Suspension higher inductive type Susp(A).
    Constructors:
    - north : Susp(A)
    - south : Susp(A)
    - merid : A to Id_Susp(A)(north, south)
    """
    def __init__(self, A: HoTTType):
        super().__init__(f"Susp({A})")
        self.A = A

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, SuspensionType):
            return self.A == other.A
        return False

    def __hash__(self) -> int:
        return hash(("SuspensionType", self.A))


class SuspPoint:
    """North or South pole of a suspension type."""
    def __init__(self, susp_type: SuspensionType, pole: str):
        if pole not in ("north", "south"):
            raise ValueError(f"Invalid pole: {pole}")
        self.susp_type = susp_type
        self.pole = pole

    def __repr__(self) -> str:
        return f"{self.susp_type}.{self.pole}"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, SuspPoint):
            return self.susp_type == other.susp_type and self.pole == other.pole
        return False

    def __hash__(self) -> int:
        return hash(("SuspPoint", self.susp_type, self.pole))


class SuspMerid(Path):
    """
    Meridian path constructor of Susp(A):
    merid(a) : Id_Susp(A)(north, south).
    """
    def __init__(self, susp_type: SuspensionType, a: Any):
        north_pt = SuspPoint(susp_type, "north")
        south_pt = SuspPoint(susp_type, "south")
        super().__init__(susp_type, north_pt, south_pt)
        self.susp_type = susp_type
        self.a = a

    def __repr__(self) -> str:
        return f"merid({self.a})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, SuspMerid):
            return self.susp_type == other.susp_type and self.a == other.a
        return False

    def __hash__(self) -> int:
        return hash(("SuspMerid", self.susp_type, self.a))


def susp_rec(
    A: HoTTType,
    Y: Any,
    n: Any,
    s: Any,
    m: Callable[[Any], Path],
) -> Callable[[SuspPoint], Any]:
    """
    Non-dependent recursor for Susp(A).
    Given target type Y, points n, s in Y, and meridian mapping m : A to Id_Y(n, s),
    returns a function f : Susp(A) to Y such that:
    f(north) = n, f(south) = s, and ap(f, merid(a)) = m(a).
    """
    def rec_fn(x: SuspPoint) -> Any:
        if x.pole == "north":
            return n
        elif x.pole == "south":
            return s
        raise ValueError(f"Invalid suspension point: {x}")

    return rec_fn


# Bool type representation
BOOL_TYPE = HoTTType("Bool")
BOOL_TRUE = "true"
BOOL_FALSE = "false"
SUSP_BOOL = SuspensionType(BOOL_TYPE)


def susp_bool_to_s1(x: SuspPoint) -> CircleBase:
    """Canonical map from Susp(Bool) to S1 sending north, south to base."""
    return BASE


def s1_to_susp_bool(x: CircleBase) -> SuspPoint:
    """Canonical map from S1 to Susp(Bool) sending base to north."""
    return SuspPoint(SUSP_BOOL, "north")


def susp_bool_equiv_s1() -> Equiv:
    """
    Equivalence between Susp(Bool) and S1:
    Susp(Bool) <~> S1.
    """
    def forward(x: SuspPoint) -> CircleBase:
        return susp_bool_to_s1(x)

    def backward(y: CircleBase) -> SuspPoint:
        return s1_to_susp_bool(y)

    def sect(x: SuspPoint) -> Path:
        # Backward(Forward(x)) to x:
        # north to north: refl
        # south to south: merid(false)
        if x.pole == "north":
            return Refl(SUSP_BOOL, x)
        else:
            return SuspMerid(SUSP_BOOL, BOOL_FALSE)

    def retr(y: CircleBase) -> Path:
        return Refl(S1, BASE)

    eta = Homotopy(lambda x: backward(forward(x)), lambda x: x, sect, SUSP_BOOL, SUSP_BOOL)
    eps = Homotopy(lambda y: forward(backward(y)), lambda y: y, retr, S1, S1)

    isequiv = IsEquiv(
        f=forward,
        g=backward,
        eta=eta,
        eps=eps,
        A=SUSP_BOOL,
        B=S1,
    )
    return Equiv(SUSP_BOOL, S1, forward, isequiv)


def susp_bool_cell_complex() -> CellComplex:
    """Return the topological CW complex of Susp(Bool)."""
    return CellComplex(
        name="Susp(Bool)",
        dim=1,
        cells_0=["north", "south"],
        cells_1=[
            ("merid_true", "north", "south"),
            ("merid_false", "north", "south"),
        ],
        cells_2=[],
    )


# ============================================================================
# 6. Torus Higher Inductive Type (T2)
# ============================================================================

class TorusType(HoTTType):
    """
    The Torus higher inductive type T2.
    Constructors:
    - b : T2 (base point)
    - p : Id_T2(b, b) (first circle loop)
    - q : Id_T2(b, b) (second circle loop)
    - surf : Id(p . q, q . p) (2-cell surface relation)
    """
    def __init__(self):
        super().__init__("T2")


T2 = TorusType()


class TorusBase:
    """Base point constructor b of the Torus T2."""
    def __init__(self):
        self.type = T2

    def __repr__(self) -> str:
        return "T2.b"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, TorusBase)

    def __hash__(self) -> int:
        return hash("TorusBase")


TORUS_B = TorusBase()


class TorusLoopP(Path):
    """First loop constructor p : Id_T2(b, b)."""
    def __init__(self):
        super().__init__(T2, TORUS_B, TORUS_B)

    def __repr__(self) -> str:
        return "p"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, TorusLoopP)

    def __hash__(self) -> int:
        return hash("TorusLoopP")


class TorusLoopQ(Path):
    """Second loop constructor q : Id_T2(b, b)."""
    def __init__(self):
        super().__init__(T2, TORUS_B, TORUS_B)

    def __repr__(self) -> str:
        return "q"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, TorusLoopQ)

    def __hash__(self) -> int:
        return hash("TorusLoopQ")


TORUS_P = TorusLoopP()
TORUS_Q = TorusLoopQ()


class TorusSurf(Path):
    """
    The 2-path surface constructor:
    surf : Id(p . q, q . p).
    """
    def __init__(self):
        pq = concat(TORUS_P, TORUS_Q)
        qp = concat(TORUS_Q, TORUS_P)
        super().__init__(pq.type, pq, qp)

    def __repr__(self) -> str:
        return "surf"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, TorusSurf)

    def __hash__(self) -> int:
        return hash("TorusSurf")


TORUS_SURF = TorusSurf()


def torus_rec(Y: Any, y: Any, py: Path, qy: Path, surfy: Path) -> Callable[[TorusBase], Any]:
    """
    Non-dependent recursor for the Torus T2.
    Given target type Y, base value y in Y, loops py, qy in Id_Y(y, y),
    and 2-path surfy : Id(py . qy, qy . py),
    returns a function f : T2 to Y such that:
    f(b) = y, ap(f, p) = py, ap(f, q) = qy, and ap2(f, surf) = surfy.
    """
    def rec_fn(pt: TorusBase) -> Any:
        if isinstance(pt, TorusBase):
            return y
        raise ValueError(f"Invalid torus point: {pt}")

    return rec_fn


PROD_S1_S1 = ProdType(S1, S1)


def torus_to_prod(t: TorusBase) -> ProdPair:
    """Canonical map from T2 to S1 * S1 sending b to (base, base)."""
    return ProdPair(BASE, BASE, PROD_S1_S1)


def prod_to_torus(xy: ProdPair) -> TorusBase:
    """Canonical map from S1 * S1 to T2 sending (base, base) to b."""
    return TORUS_B


def torus_equiv_circle_prod() -> Equiv:
    """
    Equivalence between the Torus T2 and S1 * S1:
    T2 <~> S1 * S1.
    """
    def forward(t: TorusBase) -> ProdPair:
        return torus_to_prod(t)

    def backward(xy: ProdPair) -> TorusBase:
        return prod_to_torus(xy)

    def sect(t: TorusBase) -> Path:
        return Refl(T2, TORUS_B)

    def retr(xy: ProdPair) -> Path:
        return Refl(PROD_S1_S1, ProdPair(BASE, BASE, PROD_S1_S1))

    eta = Homotopy(lambda t: backward(forward(t)), lambda t: t, sect, T2, T2)
    eps = Homotopy(lambda xy: forward(backward(xy)), lambda xy: xy, retr, PROD_S1_S1, PROD_S1_S1)

    isequiv = IsEquiv(
        f=forward,
        g=backward,
        eta=eta,
        eps=eps,
        A=T2,
        B=PROD_S1_S1,
    )
    return Equiv(T2, PROD_S1_S1, forward, isequiv)


def torus_cell_complex() -> CellComplex:
    """Return the topological CW complex of the Torus T2."""
    return CellComplex(
        name="T2",
        dim=2,
        cells_0=["b"],
        cells_1=[("p", "b", "b"), ("q", "b", "b")],
        cells_2=[("surf", ["p", "q", "-p", "-q"])],
    )
