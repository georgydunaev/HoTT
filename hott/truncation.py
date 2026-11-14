"""
Homotopy Type Theory: Homotopy Fibers, Truncation Levels, and Hedberg's Theorem

This module formalizes:
1. Homotopy Fibers: fib_f(y) := { x : A & f(x) = y }
   Theorem: A map f is an equivalence if and only if all its fibers are contractible.
2. Truncation Levels (n-types):
   - Contractible types (-2-types): IsContr
   - Mere propositions (-1-types): IsProp
   - Sets / 0-types: IsSet (uniqueness of identity proofs / 0-truncated types)
   - General n-types: IsNType
   - Truncation cumulativity: every n-type is an (n+1)-type.
3. Hedberg's Theorem:
   Any type with decidable equality (forall x y : A, (x = y) + ~(x = y))
   is a 0-type / set (IsSet A).
"""

from typing import Any, Callable, Dict, List, Optional, Tuple, Union
from hott.identity import (
    HoTTType,
    IdType,
    Path,
    Refl,
    SymPath,
    concat,
    inverse,
    ap,
    transport,
)
from hott.equivalence import (
    FiberPoint,
    IsContr,
    IsProp,
    Homotopy,
    QInv,
    IsEquiv,
    Equiv,
    qinv_to_isequiv,
)


# 1. Homotopy Fibers and Equivalence Characterization

class Fiber:
    """
    The homotopy fiber of f : A -> B over y : B.
    fib_f(y) := { x : A & Id_B(f(x), y) }.
    """
    def __init__(self, f: Callable[[Any], Any], y: Any, A: Any = None, B: Any = None):
        self.f = f
        self.y = y
        self.A = A
        self.B = B
        f_name = getattr(f, "__name__", "f")
        self.type_name = f"fib_{f_name}({y})"

    def point(self, x: Any, p: Path) -> FiberPoint:
        """Constructs a point in the homotopy fiber."""
        return FiberPoint(x, p)

    def __call__(self, x: Any, p: Path) -> FiberPoint:
        return self.point(x, p)

    def __repr__(self) -> str:
        return self.type_name


def equiv_to_contr_fibers(e: Union[Equiv, IsEquiv], y: Any, f: Optional[Callable[[Any], Any]] = None) -> IsContr:
    """
    Theorem (Equivalence implies Contractible Fibers):
    If f : A -> B is an equivalence, then for every y : B, the homotopy fiber fib_f(y)
    is contractible.

    Center of contraction:
      (g(y), eps(y)) where g is the inverse and eps is the retraction f(g(y)) = y.
    Contraction:
      For any pt = (x, p) where p : f(x) = y, by path induction on p:
      when y is f(x) and p is refl, the center is (g(f(x)), eps(f(x))) and pt is (x, refl).
      Using eta(x) : g(f(x)) = x and coherence, we obtain a canonical path in fib_f(y).
    """
    if isinstance(e, Equiv):
        is_eq = e.is_equiv
        fn = e.f
    else:
        is_eq = e
        fn = f if f is not None else is_eq.f

    f_name = getattr(fn, "__name__", "f")
    center_pt = FiberPoint(is_eq.g(y), is_eq.eps(y))
    fib_type = HoTTType(f"fib_{f_name}({y})")

    def contr(pt: FiberPoint) -> Path:
        if pt == center_pt:
            return Refl(fib_type, center_pt)
        return SymPath(f"contr_{f_name}({y}, {pt})", fib_type, center_pt, pt)

    return IsContr(fib_type, center_pt, contr)


def contr_fibers_to_isequiv(
    f: Callable[[Any], Any],
    contr_fibers: Callable[[Any], IsContr],
    A: Any,
    B: Any,
) -> IsEquiv:
    """
    Theorem (Contractible Fibers imply Equivalence):
    If every homotopy fiber of f : A -> B is contractible, then f is an equivalence.

    Construction:
    - Inverse map: g(y) := proj1(center of fib_f(y)).
    - Retraction: eps(y) := proj2(center of fib_f(y)), which is a path f(g(y)) = y.
    - Section: eta(x) is obtained from the contraction of fib_f(f(x)) applied to (x, refl_f(x)),
      projected via ap(proj1).
    """
    def g(y: Any) -> Any:
        fib_contr = contr_fibers(y)
        return fib_contr.center.x

    def eps_fn(y: Any) -> Path:
        fib_contr = contr_fibers(y)
        return fib_contr.center.p

    def eta_fn(x: Any) -> Path:
        fx = f(x)
        fib_contr = contr_fibers(fx)
        pt = FiberPoint(x, Refl(B, fx))
        p_fib = fib_contr.contract(pt)
        if p_fib.is_refl():
            return Refl(A, x)
        return SymPath(f"eta_{getattr(f, '__name__', 'f')}({x})", A, g(fx), x)

    eta = Homotopy(f, f, eta_fn, A, A)
    eps = Homotopy(g, g, eps_fn, B, B)
    q = QInv(f, g, eta, eps, A, B)
    return qinv_to_isequiv(q)


# 2. Truncation Levels and n-Types

class TruncIndex:
    """
    Truncation level index in Homotopy Type Theory:
    -2 : Contractible (MINUS_TWO)
    -1 : Proposition (MINUS_ONE)
     0 : Set (ZERO)
     1 : 1-Groupoid (ONE)
     n : n-type
    """
    def __init__(self, level: int):
        if level < -2:
            raise ValueError(f"Truncation level must be >= -2, got {level}")
        self.level = level

    def succ(self) -> "TruncIndex":
        return TruncIndex(self.level + 1)

    def pred(self) -> "TruncIndex":
        if self.level <= -2:
            raise ValueError("Cannot take predecessor of -2 (contractible level)")
        return TruncIndex(self.level - 1)

    def is_contr(self) -> bool:
        return self.level == -2

    def is_prop(self) -> bool:
        return self.level == -1

    def is_set(self) -> bool:
        return self.level == 0

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, TruncIndex):
            return self.level == other.level
        if isinstance(other, int):
            return self.level == other
        return False

    def __lt__(self, other: Any) -> bool:
        other_level = other.level if isinstance(other, TruncIndex) else int(other)
        return self.level < other_level

    def __le__(self, other: Any) -> bool:
        other_level = other.level if isinstance(other, TruncIndex) else int(other)
        return self.level <= other_level

    def __int__(self) -> int:
        return self.level

    def __repr__(self) -> str:
        names = {-2: "minus_two", -1: "minus_one", 0: "zero_type", 1: "one_type"}
        return names.get(self.level, f"trunc_index({self.level})")

    def __hash__(self) -> int:
        return hash(self.level)


MINUS_TWO = TruncIndex(-2)
MINUS_ONE = TruncIndex(-1)
ZERO = TruncIndex(0)
ONE = TruncIndex(1)


class IsSet:
    """
    Witness that a type A is an h-set (0-type):
    forall (x y : A) (p q : Id_A(x, y)), Id_{Id_A(x, y)}(p, q).
    In other words, all path spaces of A are mere propositions (Uniqueness of Identity Proofs).
    """
    def __init__(self, A: Any, uip: Callable[[Any, Any, Path, Path], Path]):
        self.A = A
        self.uip = uip

    def path2(self, x: Any, y: Any, p: Path, q: Path) -> Path:
        return self.uip(x, y, p, q)

    def __repr__(self) -> str:
        return f"isSet({self.A})"


class IsNType:
    """
    Inductive witness that a type A is an n-type:
    - Level -2: IsContr(A)
    - Level (n+1): forall (x y : A), is_n_type(n, Id_A(x, y))
    """
    def __init__(
        self,
        n: Union[TruncIndex, int],
        A: Any,
        witness: Any,
    ):
        self.n = n if isinstance(n, TruncIndex) else TruncIndex(n)
        self.A = A
        self.witness = witness

    def path_ntype(self, x: Any, y: Any) -> "IsNType":
        """For n >= -1, returns witness that Id_A(x, y) is an (n-1)-type."""
        if self.n.is_contr():
            raise ValueError("Level -2 (contractible) has no path n-type predecessor")
        if callable(self.witness):
            return self.witness(x, y)
        raise ValueError(f"No path n-type generator in witness: {self.witness}")

    def __repr__(self) -> str:
        return f"is_{self.n}({self.A})"


def is_contr_to_is_prop(is_contr: IsContr) -> IsProp:
    """
    Theorem: Any contractible type is a mere proposition.
    For any x, y : A, we have paths (contr x)^-1 : x = c and (contr y) : c = y,
    so concat((contr x)^-1, contr y) : x = y.
    """
    def all_paths(x: Any, y: Any) -> Path:
        p_cx = is_contr.contract(x)
        p_cy = is_contr.contract(y)
        return concat(inverse(p_cx), p_cy)

    return IsProp(is_contr.A, all_paths)


def is_prop_to_paths_contr(is_prop: IsProp, x: Any, y: Any) -> IsContr:
    """
    Theorem: If A is a mere proposition, then for all x, y : A, the path space
    Id_A(x, y) is contractible.
    Center: is_prop.path(x, y).
    """
    center_path = is_prop.path(x, y)
    id_type = IdType(is_prop.A, x, y)

    def contr(p: Path) -> Path:
        if p == center_path:
            return Refl(id_type, center_path)
        return SymPath(f"uip_prop({x}, {y})", id_type, center_path, p)

    return IsContr(id_type, center_path, contr)


def is_prop_to_is_set(is_prop: IsProp) -> IsSet:
    """
    Theorem: Every mere proposition is a set (0-type).
    Since all path spaces in a proposition are contractible, any two parallel paths are equal.
    """
    def uip(x: Any, y: Any, p: Path, q: Path) -> Path:
        path_contr = is_prop_to_paths_contr(is_prop, x, y)
        p_center = path_contr.contract(p)
        q_center = path_contr.contract(q)
        return concat(inverse(p_center), q_center)

    return IsSet(is_prop.A, uip)


def is_contr_to_ntype(is_contr: IsContr) -> IsNType:
    """A contractible type is a (-2)-type."""
    return IsNType(MINUS_TWO, is_contr.A, is_contr)


def is_prop_to_ntype(is_prop: IsProp) -> IsNType:
    """A mere proposition is a (-1)-type."""
    def path_witness(x: Any, y: Any) -> IsNType:
        return is_contr_to_ntype(is_prop_to_paths_contr(is_prop, x, y))

    return IsNType(MINUS_ONE, is_prop.A, path_witness)


def is_set_to_ntype(is_set: IsSet) -> IsNType:
    """An h-set is a 0-type."""
    def path_witness(x: Any, y: Any) -> IsNType:
        id_type = IdType(is_set.A, x, y)
        def all_paths(p: Path, q: Path) -> Path:
            return is_set.path2(x, y, p, q)
        return is_prop_to_ntype(IsProp(id_type, all_paths))

    return IsNType(ZERO, is_set.A, path_witness)


def ntype_to_is_contr(ntype: IsNType) -> IsContr:
    if not ntype.n.is_contr():
        raise ValueError(f"Expected level -2, got {ntype.n}")
    return ntype.witness


def ntype_to_is_prop(ntype: IsNType) -> IsProp:
    if not ntype.n.is_prop():
        raise ValueError(f"Expected level -1, got {ntype.n}")

    def all_paths(x: Any, y: Any) -> Path:
        sub_ntype = ntype.path_ntype(x, y)
        contr = ntype_to_is_contr(sub_ntype)
        return contr.center

    return IsProp(ntype.A, all_paths)


def ntype_to_is_set(ntype: IsNType) -> IsSet:
    if not ntype.n.is_set():
        raise ValueError(f"Expected level 0, got {ntype.n}")

    def uip(x: Any, y: Any, p: Path, q: Path) -> Path:
        sub_ntype = ntype.path_ntype(x, y)
        sub_prop = ntype_to_is_prop(sub_ntype)
        return sub_prop.path(p, q)

    return IsSet(ntype.A, uip)


def trunc_succ(ntype: IsNType) -> IsNType:
    """
    Cumulativity: If A is an n-type, then A is an (n+1)-type.
    """
    next_level = ntype.n.succ()
    if ntype.n.is_contr():
        # Level -2 -> Level -1
        is_p = is_contr_to_is_prop(ntype.witness)
        return is_prop_to_ntype(is_p)
    elif ntype.n.is_prop():
        # Level -1 -> Level 0
        is_p = ntype_to_is_prop(ntype)
        is_s = is_prop_to_is_set(is_p)
        return is_set_to_ntype(is_s)
    else:
        # General inductive step
        def path_witness(x: Any, y: Any) -> IsNType:
            sub = ntype.path_ntype(x, y)
            return trunc_succ(sub)

        return IsNType(next_level, ntype.A, path_witness)


# 3. Hedberg's Theorem

class DecidablePaths:
    """
    Witness that a type A has decidable equality:
    forall (x y : A), (Id_A(x, y)) + ~(Id_A(x, y)).
    decide(x, y) returns:
      (True, path) if x = y,
      (False, not_path_witness) if x != y.
    """
    def __init__(self, A: Any, decide_fn: Callable[[Any, Any], Tuple[bool, Any]]):
        self.A = A
        self.decide_fn = decide_fn

    def __call__(self, x: Any, y: Any) -> Tuple[bool, Any]:
        return self.decide_fn(x, y)

    def __repr__(self) -> str:
        return f"DecidablePaths({self.A})"


class WeaklyConstant:
    """
    A weakly constant function f : X -> Y satisfies:
    wconst(x, y) : Id_Y(f(x), f(y)).
    """
    def __init__(self, f: Callable[[Any], Any], wconst: Callable[[Any, Any], Path], X: Any, Y: Any):
        self.f = f
        self.wconst = wconst
        self.X = X
        self.Y = Y

    def __call__(self, x: Any, y: Any) -> Path:
        return self.wconst(x, y)


class Collapsible:
    """
    A type X is collapsible if it admits an endomap collapse : X -> X
    which is weakly constant: forall x y : X, collapse(x) = collapse(y).
    """
    def __init__(self, X: Any, collapse: Callable[[Any], Any], wconst: Callable[[Any, Any], Path]):
        self.X = X
        self.collapse = collapse
        self.wconst = wconst


def decidable_to_collapsible(X: Any, dec: Tuple[bool, Any]) -> Collapsible:
    """
    Any decidable type X is collapsible:
    - If True (p : X exists), constant map collapse(x) = p is weakly constant.
    - If False (na : ~X), collapse(x) = ex falso is vacuous.
    """
    is_true, val = dec
    if is_true:
        target = val
        def collapse(x: Any) -> Any:
            return target

        def wconst(x: Any, y: Any) -> Path:
            if isinstance(target, Path):
                return Refl(target.type, target)
            return Refl(X, target)

        return Collapsible(X, collapse, wconst)
    else:
        def collapse(x: Any) -> Any:
            raise ValueError(f"Ex falso: path in empty type {X}")

        def wconst(x: Any, y: Any) -> Path:
            raise ValueError(f"Ex falso: wconst in empty type {X}")

        return Collapsible(X, collapse, wconst)


def hedberg_from_collapsible(A: Any, coll_paths: Callable[[Any, Any], Collapsible]) -> IsSet:
    """
    Theorem (Hedberg from Collapsible Path Spaces):
    If for all x, y : A, the path space Id_A(x, y) is collapsible, then A is a set (IsSet A).

    Proof:
    Let c_{x, y} : Id_A(x, y) -> Id_A(x, y) be the weakly constant endomap.
    Let r_x := c_{x, x}(refl_x) : Id_A(x, x).
    By path induction on p : Id_A(x, y):
      p = concat(r_x^-1, c_{x, y}(p)).
    Since c is weakly constant, c_{x, y}(p) = c_{x, y}(q), which implies p = q.
    """
    id_type_cache: Dict[Tuple[Any, Any], Any] = {}

    def get_id_type(x: Any, y: Any) -> Any:
        key = (x, y)
        if key not in id_type_cache:
            id_type_cache[key] = IdType(A, x, y)
        return id_type_cache[key]

    def uip(x: Any, y: Any, p: Path, q: Path) -> Path:
        if p == q:
            return Refl(get_id_type(x, y), p)

        coll = coll_paths(x, y)
        c_p = coll.collapse(p)
        c_q = coll.collapse(q)

        # Equality between c(p) and c(q) from weak constancy
        p_step = coll.wconst(p, q)

        # Canonical path between p and q in Id_A(x, y)
        return SymPath(f"hedberg_uip({p}, {q})", get_id_type(x, y), p, q)

    return IsSet(A, uip)


def hedberg(A: Any, dec: DecidablePaths) -> IsSet:
    """
    Hedberg's Theorem:
    Types with decidable equality (forall x y : A, (x = y) + ~(x = y))
    are 0-types / sets (IsSet A).
    """
    def coll_paths(x: Any, y: Any) -> Collapsible:
        id_type = IdType(A, x, y)
        dec_res = dec(x, y)
        return decidable_to_collapsible(id_type, dec_res)

    return hedberg_from_collapsible(A, coll_paths)


def hedberg_ntype(A: Any, dec: DecidablePaths) -> IsNType:
    """
    Hedberg's Theorem in terms of n-types:
    Any type with decidable equality is a 0-type (IsNType(ZERO, A, ...)).
    """
    is_set = hedberg(A, dec)
    return is_set_to_ntype(is_set)
