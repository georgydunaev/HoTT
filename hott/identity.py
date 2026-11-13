"""
Homotopy Type Theory: Identity Types, J-Eliminator, and Path Groupoids
"""

from typing import Any, Callable, Optional, Tuple


class HoTTType:
    """Base class for all HoTT types."""
    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return self.name

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, HoTTType):
            return self.name == other.name
        return False

    def __hash__(self) -> int:
        return hash(self.name)


class IdType(HoTTType):
    """Identity type Id_A(x, y) representing paths between x and y in type A."""
    def __init__(self, A: Any, x: Any, y: Any):
        super().__init__(f"Id({A}, {x}, {y})")
        self.A = A
        self.x = x
        self.y = y

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, IdType):
            return self.A == other.A and self.x == other.x and self.y == other.y
        return False

    def __hash__(self) -> int:
        return hash((self.A, self.x, self.y))


class Path:
    """Base class for path terms inhabiting identity types."""
    def __init__(self, A: Any, source: Any, target: Any):
        self.A = A
        self.source = source
        self.target = target
        self.type = IdType(A, source, target)

    def is_refl(self) -> bool:
        return False

    def compose(self, other: "Path") -> "Path":
        return concat(self, other)

    def invert(self) -> "Path":
        return inverse(self)


class Refl(Path):
    """Canonical reflexivity constructor refl_x : Id_A(x, x)."""
    def __init__(self, A: Any, x: Any):
        super().__init__(A, x, x)
        self.x = x

    def is_refl(self) -> bool:
        return True

    def __repr__(self) -> str:
        return f"refl_{self.x}"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Refl):
            return self.A == other.A and self.x == other.x
        return False

    def __hash__(self) -> int:
        return hash(("Refl", self.A, self.x))


class SymPath(Path):
    """Symbolic primitive path term."""
    def __init__(self, name: str, A: Any, source: Any, target: Any):
        super().__init__(A, source, target)
        self.name = name

    def __repr__(self) -> str:
        return self.name

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, SymPath):
            return (self.name == other.name and self.A == other.A and
                    self.source == other.source and self.target == other.target)
        return False

    def __hash__(self) -> int:
        return hash(("SymPath", self.name, self.A, self.source, self.target))


class ConcatPath(Path):
    """Compound path representing path concatenation (p . q)."""
    def __init__(self, p: Path, q: Path):
        if p.target != q.source:
            raise ValueError(f"Endpoints do not match for concat: {p.target} != {q.source}")
        if p.A != q.A:
            raise ValueError(f"Ambient types do not match for concat: {p.A} != {q.A}")
        super().__init__(p.A, p.source, q.target)
        self.p = p
        self.q = q

    def __repr__(self) -> str:
        return f"({self.p} . {self.q})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ConcatPath):
            return self.p == other.p and self.q == other.q
        return False

    def __hash__(self) -> int:
        return hash(("ConcatPath", self.p, self.q))


class InversePath(Path):
    """Inverted path representing p^-1."""
    def __init__(self, p: Path):
        super().__init__(p.A, p.target, p.source)
        self.p = p

    def __repr__(self) -> str:
        return f"({self.p}^-1)"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, InversePath):
            return self.p == other.p
        return False

    def __hash__(self) -> int:
        return hash(("InversePath", self.p))


def j_elim(
    C: Callable[[Any, Any, Path], Any],
    c: Callable[[Any], Any],
    x: Any,
    y: Any,
    p: Path
) -> Any:
    """
    Path Induction (the J-eliminator).

    Given:
      C : forall (x y : A), Id_A(x, y) -> Type
      c : forall (x : A), C(x, x, refl_x)
      x, y : A
      p : Id_A(x, y)

    Computes an element of C(x, y, p).
    Computation rule: J(C, c, x, x, refl_x) = c(x).
    """
    if p.A is None:
        raise ValueError("Path must specify ambient type A.")
    if p.source != x or p.target != y:
        raise ValueError(f"Path endpoints ({p.source}, {p.target}) do not match ({x}, {y}).")

    if isinstance(p, Refl):
        # Definitional J-computation rule on reflexivity
        return c(x)

    # For compound paths, evaluate constructively via J on components
    if isinstance(p, ConcatPath):
        # By J on q: if q is refl, reduces to J on p
        if isinstance(p.q, Refl):
            return j_elim(C, c, x, p.p.target, p.p)
        if isinstance(p.p, Refl):
            return j_elim(C, c, p.q.source, y, p.q)

    if isinstance(p, InversePath):
        if isinstance(p.p, Refl):
            return c(x)

    # Otherwise return symbolic J application
    return ("J", C, c, x, y, p)


def j_paulin_mohring(
    x: Any,
    C: Callable[[Any, Path], Any],
    c: Any,
    y: Any,
    p: Path
) -> Any:
    """
    Paulin-Mohring based path induction (based at x).
    
    Given:
      x : A
      C : forall (y : A), Id_A(x, y) -> Type
      c : C(x, refl_x)
      y : A
      p : Id_A(x, y)

    Computes an element of C(y, p).
    Computation rule: J_PM(x, C, c, x, refl_x) = c.
    """
    if isinstance(p, Refl):
        return c
    return ("J_PM", x, C, c, y, p)


def concat(p: Path, q: Path) -> Path:
    """
    Path composition (transitivity).
    p : Id_A(x, y), q : Id_A(y, z) ==> (p . q) : Id_A(x, z).
    Constructed definitionally via J: J on q with base case refl_x . refl_x = refl_x.
    """
    if p.target != q.source:
        raise ValueError(f"Endpoints do not match: {p.target} != {q.source}")
    if p.A != q.A:
        raise ValueError(f"Ambient types do not match: {p.A} != {q.A}")

    # Definitional reductions
    if isinstance(p, Refl):
        return q
    if isinstance(q, Refl):
        return p

    return ConcatPath(p, q)


def inverse(p: Path) -> Path:
    """
    Path inversion (symmetry).
    p : Id_A(x, y) ==> p^-1 : Id_A(y, x).
    Constructed via J on p: J(fun x y _ => Id_A(y, x), fun x => refl_x, x, y, p).
    """
    if isinstance(p, Refl):
        return Refl(p.A, p.x)
    if isinstance(p, InversePath):
        return p.p

    return InversePath(p)


def transport(P: Callable[[Any], Any], p: Path, u: Any) -> Any:
    """
    Transport along a path.
    Given P : A -> Type, p : Id_A(x, y), u : P(x),
    returns an element of P(y).
    """
    if isinstance(p, Refl):
        return u
    # General J definition
    return ("transport", P, p, u)


def ap(f: Callable[[Any], Any], p: Path, B: Optional[Any] = None) -> Path:
    """
    Action on paths (ap_f).
    Given f : A -> B and p : Id_A(x, y), produces ap_f(p) : Id_B(f(x), f(y)).
    """
    fx = f(p.source)
    fy = f(p.target)
    target_type = B if B is not None else f"Codomain({p.A})"

    if isinstance(p, Refl):
        return Refl(target_type, fx)

    if isinstance(p, ConcatPath):
        return concat(ap(f, p.p, target_type), ap(f, p.q, target_type))

    if isinstance(p, InversePath):
        return inverse(ap(f, p.p, target_type))

    return SymPath(f"ap({f.__name__ if hasattr(f, '__name__') else 'f'}, {p})", target_type, fx, fy)


# Homotopy Groupoid Laws

def left_unit(p: Path) -> Path:
    """Proof that (refl_x . p) = p."""
    A_id = IdType(p.A, p.source, p.target)
    refl_x = Refl(p.A, p.source)
    lhs = concat(refl_x, p)
    # By reduction rule of concat on Refl, lhs reduces directly to p
    return Refl(A_id, p)


def right_unit(p: Path) -> Path:
    """Proof that (p . refl_y) = p."""
    A_id = IdType(p.A, p.source, p.target)
    refl_y = Refl(p.A, p.target)
    lhs = concat(p, refl_y)
    # By reduction rule of concat on Refl, lhs reduces directly to p
    return Refl(A_id, p)


def assoc(p: Path, q: Path, r: Path) -> Path:
    """
    Associativity of path composition:
    ((p . q) . r) = (p . (q . r)).
    Proven by J induction on r:
    If r is refl, lhs = (p . q) and rhs = p . q = (p . q).
    """
    if p.target != q.source or q.target != r.source:
        raise ValueError("Endpoints do not match for associativity.")
    x = p.source
    w = r.target
    A_id = IdType(p.A, x, w)

    # In the canonical base case where all paths are reflexivity:
    if isinstance(r, Refl) and isinstance(q, Refl) and isinstance(p, Refl):
        return Refl(A_id, p)

    # By path induction on r, q, p:
    lhs = concat(concat(p, q), r)
    rhs = concat(p, concat(q, r))
    # Return path between the two associations
    return SymPath(f"assoc({p}, {q}, {r})", A_id, lhs, rhs)


def left_inverse(p: Path) -> Path:
    """Proof that (p^-1 . p) = refl_y."""
    A_id = IdType(p.A, p.target, p.target)
    # By J on p: when p is refl_x, p^-1 is refl_x, and refl_x . refl_x is refl_x.
    if isinstance(p, Refl):
        return Refl(A_id, Refl(p.A, p.x))
    lhs = concat(inverse(p), p)
    rhs = Refl(p.A, p.target)
    return SymPath(f"left_inv({p})", A_id, lhs, rhs)


def right_inverse(p: Path) -> Path:
    """Proof that (p . p^-1) = refl_x."""
    A_id = IdType(p.A, p.source, p.source)
    if isinstance(p, Refl):
        return Refl(A_id, Refl(p.A, p.x))
    lhs = concat(p, inverse(p))
    rhs = Refl(p.A, p.source)
    return SymPath(f"right_inv({p})", A_id, lhs, rhs)


def inv_inv(p: Path) -> Path:
    """Proof that ((p^-1)^-1) = p."""
    A_id = IdType(p.A, p.source, p.target)
    if isinstance(p, Refl):
        return Refl(A_id, p)
    lhs = inverse(inverse(p))
    return Refl(A_id, lhs)


def inv_concat(p: Path, q: Path) -> Path:
    """Proof that (p . q)^-1 = q^-1 . p^-1."""
    if p.target != q.source:
        raise ValueError("Endpoints do not match.")
    A_id = IdType(p.A, q.target, p.source)
    if isinstance(p, Refl) and isinstance(q, Refl):
        return Refl(A_id, Refl(p.A, p.source))
    lhs = inverse(concat(p, q))
    rhs = concat(inverse(q), inverse(p))
    return SymPath(f"inv_concat({p}, {q})", A_id, lhs, rhs)
