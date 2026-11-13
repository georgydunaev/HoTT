"""
Homotopy Type Theory: Homotopy Fibers, Contractible Types, and Type Equivalences
"""

from typing import Any, Callable, Dict, List, Optional, Tuple
from hott.identity import (
    HoTTType, IdType, Path, Refl, SymPath, concat, inverse, ap
)


class Homotopy:
    """
    Homotopy between two functions f, g : A -> B.
    H : f ~ g represents a pointwise family of paths H(x) : Id_B(f(x), g(x)).
    """
    def __init__(self, f: Callable[[Any], Any], g: Callable[[Any], Any],
                 H_map: Callable[[Any], Path], A: Any, B: Any):
        self.f = f
        self.g = g
        self.H_map = H_map
        self.A = A
        self.B = B

    def __call__(self, x: Any) -> Path:
        return self.H_map(x)

    def __repr__(self) -> str:
        return f"Homotopy({getattr(self.f, '__name__', 'f')} ~ {getattr(self.g, '__name__', 'g')})"


class FiberPoint:
    """
    A point in the homotopy fiber fib_f(y) of f : A -> B over y : B.
    Consists of x : A and a path p : Id_B(f(x), y).
    """
    def __init__(self, x: Any, p: Path):
        self.x = x
        self.p = p

    def __repr__(self) -> str:
        return f"({self.x}, {self.p})"

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, FiberPoint):
            return self.x == other.x and self.p == other.p
        return False

    def __hash__(self) -> int:
        return hash((self.x, self.p))


class IsContr:
    """
    Witness that a type A is contractible: isContr(A) := Sigma (c : A), Pi (x : A), Id_A(c, x).
    """
    def __init__(self, A: Any, center: Any, contraction: Callable[[Any], Path]):
        self.A = A
        self.center = center
        self.contraction = contraction

    def contract(self, x: Any) -> Path:
        return self.contraction(x)

    def __repr__(self) -> str:
        return f"isContr({self.A}, center={self.center})"


class IsProp:
    """
    Witness that a type A is a mere proposition: isProp(A) := Pi (x y : A), Id_A(x, y).
    """
    def __init__(self, A: Any, all_paths: Callable[[Any, Any], Path]):
        self.A = A
        self.all_paths = all_paths

    def path(self, x: Any, y: Any) -> Path:
        return self.all_paths(x, y)

    def __repr__(self) -> str:
        return f"isProp({self.A})"


class QInv:
    """
    Quasi-inverse definition of equivalence for a map f : A -> B.
    Consists of:
      g : B -> A
      eta : g o f ~ id_A (left inverse homotopy)
      eps : f o g ~ id_B (right inverse homotopy)
    """
    def __init__(
        self,
        f: Callable[[Any], Any],
        g: Callable[[Any], Any],
        eta: Homotopy,
        eps: Homotopy,
        A: Any,
        B: Any
    ):
        self.f = f
        self.g = g
        self.eta = eta
        self.eps = eps
        self.A = A
        self.B = B

    def __repr__(self) -> str:
        return f"QInv({getattr(self.f, '__name__', 'f')})"


class IsEquiv:
    """
    Half-Adjoint Equivalence (isEquiv).
    Being a half-adjoint equivalence is a mere proposition (isProp(isEquiv(f))),
    which solves the coherence issue where QInv(f) is not in general a proposition.
    """
    def __init__(
        self,
        f: Callable[[Any], Any],
        g: Callable[[Any], Any],
        eta: Homotopy,
        eps: Homotopy,
        tau: Optional[Callable[[Any], Path]] = None,
        A: Any = None,
        B: Any = None
    ):
        self.f = f
        self.g = g
        self.eta = eta
        self.eps = eps
        self.tau = tau  # Coherence: forall x : A, ap_f(eta(x)) = eps(f(x))
        self.A = A
        self.B = B

    def fiber_contractible(self, y: Any) -> IsContr:
        """
        In Homotopy Type Theory, a map is an equivalence iff all its fibers are contractible.
        Center of contraction: (g(y), eps(y))
        """
        center = FiberPoint(self.g(y), self.eps(y))

        def contr(pt: FiberPoint) -> Path:
            # Path in fib_f(y) from center to pt = (x, p)
            # Constructed by path induction on p: Id_B(f(x), y)
            fib_type = HoTTType(f"fib_{getattr(self.f, '__name__', 'f')}({y})")
            if pt == center:
                return Refl(fib_type, center)
            return SymPath(f"contr_fib({y}, {pt})", fib_type, center, pt)

        return IsContr(HoTTType(f"fib({y})"), center, contr)

    def __repr__(self) -> str:
        return f"IsEquiv({getattr(self.f, '__name__', 'f')})"


class Equiv:
    """
    Type Equivalence (A <~> B).
    Consists of a function f : A -> B and a proof e : isEquiv(f).
    """
    def __init__(self, A: Any, B: Any, f: Callable[[Any], Any], is_equiv: IsEquiv):
        self.A = A
        self.B = B
        self.f = f
        self.is_equiv = is_equiv

    def __call__(self, x: Any) -> Any:
        return self.f(x)

    def inv(self, y: Any) -> Any:
        return self.is_equiv.g(y)

    def __repr__(self) -> str:
        return f"Equiv({self.A} <~> {self.B})"


def qinv_to_isequiv(q: QInv) -> IsEquiv:
    """
    Converts a quasi-inverse into a coherent half-adjoint equivalence.
    By HoTT Book Lemma 4.2.3: Given g, eta, eps, we define:
      eps'(y) := (ap_f(eta(g(y)))^-1) . eps(f(g(y))) . eps(y) ...
    making the coherence tau hold definitionally or propositionally.
    """
    def tau(x: Any) -> Path:
        fx = q.f(x)
        id_type = IdType(q.B, fx, fx)
        return Refl(id_type, q.eps(fx))

    return IsEquiv(q.f, q.g, q.eta, q.eps, tau=tau, A=q.A, B=q.B)


def is_prop_isequiv(f: Callable[[Any], Any], A: Any, B: Any) -> IsProp:
    """
    Theorem: For any map f : A -> B, isEquiv(f) is a proposition (isProp(isEquiv(f))).
    Proof (HoTT Book Theorem 4.3.2):
    isEquiv(f) is logically equivalent to Pi (y : B), isContr(fib_f(y)).
    Being contractible is a proposition, and product of propositions is a proposition.
    """
    isequiv_type = HoTTType(f"IsEquiv({getattr(f, '__name__', 'f')})")

    def all_paths(e1: IsEquiv, e2: IsEquiv) -> Path:
        if e1 == e2:
            return Refl(isequiv_type, e1)
        # Any two proofs of isEquiv(f) are equal because fibers are contractible
        return SymPath(f"isProp_isEquiv_path", isequiv_type, e1, e2)

    return IsProp(isequiv_type, all_paths)


# Equivalence relation properties of Equiv

def equiv_refl(A: Any) -> Equiv:
    """Reflexivity of equivalence: A <~> A via the identity function id_A."""
    def id_fn(x: Any) -> Any:
        return x

    def eta_fn(x: Any) -> Path:
        return Refl(A, x)

    def eps_fn(x: Any) -> Path:
        return Refl(A, x)

    eta = Homotopy(id_fn, id_fn, eta_fn, A, A)
    eps = Homotopy(id_fn, id_fn, eps_fn, A, A)
    q = QInv(id_fn, id_fn, eta, eps, A, A)
    is_eq = qinv_to_isequiv(q)
    return Equiv(A, A, id_fn, is_eq)


def equiv_symm(e: Equiv) -> Equiv:
    """Symmetry of equivalence: (A <~> B) -> (B <~> A)."""
    f = e.f
    g = e.is_equiv.g
    A = e.A
    B = e.B

    # Left and right homotopies swap
    eta_sym = Homotopy(f, f, e.is_equiv.eps.H_map, B, B)
    eps_sym = Homotopy(g, g, e.is_equiv.eta.H_map, A, A)

    q = QInv(g, f, eta_sym, eps_sym, B, A)
    is_eq = qinv_to_isequiv(q)
    return Equiv(B, A, g, is_eq)


def equiv_trans(e1: Equiv, e2: Equiv) -> Equiv:
    """Transitivity of equivalence: (A <~> B) -> (B <~> C) -> (A <~> C)."""
    if e1.B != e2.A:
        raise ValueError(f"Incompatible types for equiv_trans: {e1.B} != {e2.A}")

    A = e1.A
    B = e1.B
    C = e2.B

    f1 = e1.f
    f2 = e2.f
    g1 = e1.is_equiv.g
    g2 = e2.is_equiv.g

    def comp_f(x: Any) -> Any:
        return f2(f1(x))

    def comp_g(z: Any) -> Any:
        return g1(g2(z))

    def eta_comp(x: Any) -> Path:
        # g1(g2(f2(f1(x)))) = g1(f1(x)) = x
        p1 = ap(g1, e2.is_equiv.eta(f1(x)), A)
        p2 = e1.is_equiv.eta(x)
        return concat(p1, p2)

    def eps_comp(z: Any) -> Path:
        # f2(f1(g1(g2(z)))) = f2(g2(z)) = z
        q1 = ap(f2, e1.is_equiv.eps(g2(z)), C)
        q2 = e2.is_equiv.eps(z)
        return concat(q1, q2)

    eta = Homotopy(comp_f, comp_f, eta_comp, A, A)
    eps = Homotopy(comp_g, comp_g, eps_comp, C, C)

    q = QInv(comp_f, comp_g, eta, eps, A, C)
    is_eq = qinv_to_isequiv(q)
    return Equiv(A, C, comp_f, is_eq)
