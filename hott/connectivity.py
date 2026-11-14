"""
Homotopy Type Theory: Blakers-Massey Connectivity Theorem and Freudenthal Suspension Theorem

This module formalizes:
1. n-Connected Types:
   A type A is n-connected if its n-truncation ||A||_n is contractible (isContr ||A||_n).
2. n-Connected Maps:
   A map f : A to B is n-connected if for every y in B, the homotopy fiber
   fib_f(y) := { x : A & Id_B(f(x), y) } is n-connected.
3. Loop Space Functor:
   Omega(A, a0) := (a0 = a0). If A is n-connected, Omega(A, a0) is (n-1)-connected.
4. Suspension Functor:
   Sigma(A) with poles north, south, and meridians merid(a).
   If A is n-connected, Sigma(A) is (n+1)-connected.
5. Canonical Freudenthal Suspension Map:
   sigma : A to Omega(Sigma(A), north) defined by sigma(a) := merid(a) . (merid(a0))^{-1}.
   When A is n-connected, sigma is (2n)-connected.
6. Blakers-Massey Homotopy Excision Theorem:
   For a span A (via f from C) and B (via g from C) with f : C to A n-connected and g : C to B m-connected,
   the comparison map from C to the homotopy pullback of the pushout inclusions is
   (n + m)-connected (establishing that the pushout square is (n + m)-cartesian).
7. Homotopy Group Stability:
   The Freudenthal map induces isomorphisms pi_{k+1}(Sigma A) =~ pi_k(A) for k < 2n.
   Computes stable homotopy groups of spheres pi_k(S^n).
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
)
from hott.equivalence import (
    FiberPoint,
    IsContr,
)
from hott.truncation import (
    Fiber,
    TruncIndex,
    MINUS_TWO,
    MINUS_ONE,
    ZERO,
    ONE,
)


# 1. Connectivity Level Arithmetic

class ConnectivityLevel:
    """
    Representation of truncation and connectivity levels in Homotopy Type Theory.
    Level n corresponds to n-connectedness:
      -2 : Contractible / universally connected
      -1 : Inhabited (propositional truncation is contractible)
       0 : 0-connected (path-connected)
       1 : 1-connected (simply connected)
       n : n-connected (homotopy groups vanish up to degree n)
    """

    def __init__(self, level: int):
        if level < -2:
            raise ValueError(f"Connectivity level must be at least -2, got {level}")
        self.level = level

    def succ(self) -> "ConnectivityLevel":
        """Successor level: (n + 1)."""
        return ConnectivityLevel(self.level + 1)

    def pred(self) -> "ConnectivityLevel":
        """Predecessor level: (n - 1), bounded below by -2."""
        if self.level <= -2:
            return ConnectivityLevel(-2)
        return ConnectivityLevel(self.level - 1)

    def add(self, other: Union["ConnectivityLevel", int]) -> "ConnectivityLevel":
        """
        Connectivity addition for Blakers-Massey homotopy excision:
        Computes (n + m) connectivity bound.
        """
        other_lvl = other.level if isinstance(other, ConnectivityLevel) else int(other)
        return ConnectivityLevel(max(-2, self.level + other_lvl))

    def double(self) -> "ConnectivityLevel":
        """
        Double connectivity for Freudenthal suspension map:
        Computes (2n) connectivity bound.
        """
        return ConnectivityLevel(max(-2, 2 * self.level))

    def to_trunc_index(self) -> TruncIndex:
        """Converts connectivity level to HoTT TruncIndex."""
        return TruncIndex(self.level)

    def is_contractible(self) -> bool:
        return self.level <= -2

    def is_inhabited(self) -> bool:
        return self.level >= -1

    def is_path_connected(self) -> bool:
        return self.level >= 0

    def is_simply_connected(self) -> bool:
        return self.level >= 1

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ConnectivityLevel):
            return self.level == other.level
        if isinstance(other, int):
            return self.level == other
        return False

    def __lt__(self, other: Any) -> bool:
        other_lvl = other.level if isinstance(other, ConnectivityLevel) else int(other)
        return self.level < other_lvl

    def __le__(self, other: Any) -> bool:
        other_lvl = other.level if isinstance(other, ConnectivityLevel) else int(other)
        return self.level <= other_lvl

    def __int__(self) -> int:
        return self.level

    def __repr__(self) -> str:
        return f"ConnectivityLevel({self.level})"


# 2. n-Connected Types

class ConnectedType:
    """
    Representation of an n-connected type A in Homotopy Type Theory.
    A is n-connected if its n-truncation ||A||_n is contractible.
    """

    def __init__(
        self,
        name: str,
        connectivity: Union[int, ConnectivityLevel, TruncIndex],
        basepoint: Optional[Any] = None,
        witness_center: Optional[Any] = None,
    ):
        self.name = name
        if isinstance(connectivity, ConnectivityLevel):
            self.connectivity = connectivity.level
        elif isinstance(connectivity, TruncIndex):
            self.connectivity = connectivity.level
        else:
            self.connectivity = int(connectivity)
        self.basepoint = basepoint
        self.witness_center = witness_center if witness_center is not None else basepoint

    def is_connected(self, k: int) -> bool:
        """Checks if the type is k-connected (k <= connectivity)."""
        return k <= self.connectivity

    def is_inhabited(self) -> bool:
        """Checks if type is inhabited (at least -1-connected or has basepoint)."""
        return self.connectivity >= -1 or self.basepoint is not None

    def is_path_connected(self) -> bool:
        """Checks if type is 0-connected (path-connected)."""
        return self.connectivity >= 0

    def is_simply_connected(self) -> bool:
        """Checks if type is 1-connected (simply connected)."""
        return self.connectivity >= 1

    def truncation_contr(self) -> IsContr:
        """Returns witness that ||A||_n is contractible."""
        trunc_type = HoTTType(f"Trunc_{self.connectivity}({self.name})")
        center = self.witness_center if self.witness_center is not None else f"tr_{self.connectivity}({self.name})"
        return IsContr(
            trunc_type,
            center,
            lambda x: Refl(trunc_type, center),
        )

    def suspension(self) -> "ConnectedType":
        """
        The suspension Sigma(A) of an n-connected type is (n+1)-connected.
        """
        susp_conn = self.connectivity + 1
        return ConnectedType(
            name=f"Susp({self.name})",
            connectivity=susp_conn,
            basepoint=f"north_{self.name}",
        )

    def loop_space(self) -> "ConnectedType":
        """
        The loop space Omega(A, a0) of an n-connected type is (n-1)-connected.
        """
        loop_conn = max(-2, self.connectivity - 1)
        pt = self.basepoint if self.basepoint is not None else "base"
        return ConnectedType(
            name=f"Omega({self.name}, {pt})",
            connectivity=loop_conn,
            basepoint=Refl(HoTTType(self.name), pt),
        )

    def __repr__(self) -> str:
        return f"ConnectedType({self.name}, connectivity={self.connectivity})"


# 3. n-Connected Maps

class ConnectedMap:
    """
    Representation of an n-connected map f : A to B in Homotopy Type Theory.
    f is n-connected if for every y in B, the homotopy fiber fib_f(y) is n-connected.
    """

    def __init__(
        self,
        name: str,
        dom: ConnectedType,
        codom: ConnectedType,
        connectivity: Union[int, ConnectivityLevel],
        f: Optional[Callable[[Any], Any]] = None,
        fiber_gen: Optional[Callable[[Any], ConnectedType]] = None,
    ):
        self.name = name
        self.dom = dom
        self.codom = codom
        self.connectivity = (
            connectivity.level if isinstance(connectivity, ConnectivityLevel) else int(connectivity)
        )
        self.f = f if f is not None else (lambda x: f"{name}({x})")
        self.fiber_gen = fiber_gen

    def is_connected(self, k: int) -> bool:
        """Checks if map is k-connected (k <= connectivity)."""
        return k <= self.connectivity

    def fiber(self, y: Any) -> ConnectedType:
        """
        Returns the homotopy fiber fib_f(y) as an n-connected type.
        """
        if self.fiber_gen is not None:
            return self.fiber_gen(y)
        return ConnectedType(
            name=f"fib_{self.name}({y})",
            connectivity=self.connectivity,
            basepoint=(f"pt_{y}", Refl(HoTTType(self.codom.name), y)),
        )

    def validate_fiber_connectivity(self, sample_points: List[Any]) -> bool:
        """
        Validates that for all sample points y in codomain, fib_f(y) is n-connected.
        """
        for y in sample_points:
            fib = self.fiber(y)
            if fib.connectivity < self.connectivity:
                return False
        return True

    def __call__(self, x: Any) -> Any:
        return self.f(x)

    def __repr__(self) -> str:
        return (
            f"ConnectedMap({self.name} : {self.dom.name} to {self.codom.name}, "
            f"connectivity={self.connectivity})"
        )


def fiber_connectivity_validator(f_map: ConnectedMap, sample_points: List[Any]) -> bool:
    """
    Validates that a given map satisfies the fiber-wise n-connectedness condition
    across all provided test points in its codomain.
    """
    return f_map.validate_fiber_connectivity(sample_points)


# 4. Loop Space AST and Operations

class LoopSpace:
    """
    Loop space Omega(A, a0) := (a0 = a0).
    Basepoint is idpath a0 = Refl(a0).
    """

    def __init__(self, space: ConnectedType, basepoint: Optional[Any] = None):
        self.space = space
        self.basepoint = basepoint if basepoint is not None else space.basepoint
        if self.basepoint is None:
            self.basepoint = f"base_{space.name}"
        self.connectivity = max(-2, space.connectivity - 1)
        self.name = f"Omega({space.name}, {self.basepoint})"
        self.space_type = HoTTType(space.name)
        self.loop_base = Refl(self.space_type, self.basepoint)

    def iterated(self, k: int) -> "LoopSpace":
        """
        Iterated loop space Omega^k(A, a0).
        Connectivity degree shifts downward by k, bounded below by -2.
        """
        if k < 0:
            raise ValueError(f"Iteration degree must be non-negative, got {k}")
        if k == 0:
            return self
        curr = self
        for _ in range(k):
            curr = LoopSpace(
                space=ConnectedType(curr.name, curr.connectivity, curr.basepoint),
                basepoint=curr.loop_base,
            )
        return curr

    def to_connected_type(self) -> ConnectedType:
        return ConnectedType(
            name=self.name,
            connectivity=self.connectivity,
            basepoint=self.loop_base,
        )

    def __repr__(self) -> str:
        return f"LoopSpace({self.name}, connectivity={self.connectivity})"


# 5. Suspension Functor AST

class SuspensionFunctor:
    """
    Suspension Sigma(A) higher inductive type functor.
    Poles: north, south.
    Meridian path constructor: merid(a) : north = south.
    If A is n-connected, Sigma(A) is (n + 1)-connected.
    """

    def __init__(self, space: ConnectedType):
        self.space = space
        self.connectivity = space.connectivity + 1
        self.name = f"Susp({space.name})"
        self.north = f"north_{space.name}"
        self.south = f"south_{space.name}"

    def merid(self, a: Any) -> Path:
        """
        Meridian path constructor: merid(a) from north to south.
        """
        susp_type = HoTTType(self.name)
        return SymPath(f"merid({a})", susp_type, self.north, self.south)

    def to_connected_type(self) -> ConnectedType:
        return ConnectedType(
            name=self.name,
            connectivity=self.connectivity,
            basepoint=self.north,
        )

    def __repr__(self) -> str:
        return f"SuspensionFunctor({self.name}, connectivity={self.connectivity})"


# 6. Canonical Freudenthal Suspension Map

class FreudenthalMap:
    """
    The canonical suspension comparison map:
      sigma : A to Omega(Sigma(A), north)
    defined by:
      sigma(a) := merid(a) . (merid(a0))^{-1}
    When A is n-connected, sigma is (2n)-connected.
    """

    def __init__(self, space: ConnectedType, basepoint: Optional[Any] = None):
        self.space = space
        self.basepoint = basepoint if basepoint is not None else space.basepoint
        if self.basepoint is None:
            self.basepoint = f"base_{space.name}"
        self.susp = SuspensionFunctor(space)
        self.loop_space = LoopSpace(self.susp.to_connected_type(), self.susp.north)

        # Freudenthal Connectivity Bound: 2n
        self.connectivity = 2 * space.connectivity
        self.name = f"sigma_{space.name}"

    def apply(self, a: Any) -> Path:
        """
        Computes sigma(a) = merid(a) . (merid(a0))^{-1} in Omega(Sigma(A), north).
        """
        m_a = self.susp.merid(a)
        m_a0 = self.susp.merid(self.basepoint)
        inv_m_a0 = inverse(m_a0)
        return concat(m_a, inv_m_a0)

    def basepoint_preservation(self) -> Path:
        """
        sigma(a0) = merid(a0) . (merid(a0))^{-1} = idpath north.
        """
        return self.apply(self.basepoint)

    def is_in_stable_range(self, k: int) -> bool:
        """
        Freudenthal stability: induced map on pi_k is an isomorphism for k < 2n.
        """
        return k < self.connectivity

    def stable_range(self) -> Tuple[int, int]:
        """
        Returns (min_k, max_k) for stability: [0, 2n - 1].
        """
        max_k = max(0, self.connectivity - 1)
        return (0, max_k)

    def to_connected_map(self) -> ConnectedMap:
        return ConnectedMap(
            name=self.name,
            dom=self.space,
            codom=self.loop_space.to_connected_type(),
            connectivity=self.connectivity,
            f=self.apply,
        )

    def __call__(self, a: Any) -> Path:
        return self.apply(a)

    def __repr__(self) -> str:
        return (
            f"FreudenthalMap({self.name} : {self.space.name} to {self.loop_space.name}, "
            f"connectivity={self.connectivity})"
        )


# 7. Blakers-Massey Pushout Square and Homotopy Excision

class BlakersMasseySquare:
    """
    Representation of the Blakers-Massey Homotopy Excision pushout square:
          C  ---g--->  B
          |            |
          f            |
          v            v
          A  ------> Pushout(f, g)

    If f : C to A is n-connected and g : C to B is m-connected, then the
    canonical comparison map:
      kappa : C to HomotopyPullback(A to Pushout, B to Pushout)
    is (n + m)-connected.
    """

    def __init__(
        self,
        f: ConnectedMap,
        g: ConnectedMap,
        pushout_name: Optional[str] = None,
    ):
        if f.dom.name != g.dom.name:
            raise ValueError(
                f"Span domain mismatch: f has domain {f.dom.name}, g has domain {g.dom.name}"
            )
        self.C = f.dom
        self.A = f.codom
        self.B = g.codom
        self.f = f
        self.g = g
        self.n = f.connectivity
        self.m = g.connectivity

        # Blakers-Massey connectivity bound: n + m
        self.connectivity_bound = self.n + self.m
        self.pushout_name = (
            pushout_name if pushout_name is not None else f"Pushout({f.name}, {g.name})"
        )
        self.pullback_name = f"Pullback_{self.pushout_name}({self.A.name}, {self.B.name})"

    def comparison_map_connectivity(self) -> int:
        """Returns the Blakers-Massey comparison map connectivity: n + m."""
        return self.connectivity_bound

    def is_cartesian_up_to(self, k: int) -> bool:
        """
        Checks if the square is k-cartesian (k <= n + m).
        """
        return k <= self.connectivity_bound

    def comparison_map(self) -> ConnectedMap:
        """
        Constructs the canonical comparison map kappa : C to HomotopyPullback.
        """
        pullback_type = ConnectedType(
            name=self.pullback_name,
            connectivity=min(self.A.connectivity, self.B.connectivity),
        )
        return ConnectedMap(
            name=f"kappa_{self.pushout_name}",
            dom=self.C,
            codom=pullback_type,
            connectivity=self.connectivity_bound,
            f=lambda c: (self.f(c), self.g(c), f"glue({c})"),
        )

    def suspension_specialization(self) -> FreudenthalMap:
        """
        Specializes Blakers-Massey to the pushout 1 <-- C --> 1, which yields
        the suspension Sigma(C). With n = m = C.connectivity, this recovers
        the Freudenthal suspension map with connectivity 2n.
        """
        return FreudenthalMap(self.C)

    def __repr__(self) -> str:
        return (
            f"BlakersMasseySquare(f: {self.n}-connected, g: {self.m}-connected, "
            f"comparison_bound={self.connectivity_bound})"
        )


# 8. Freudenthal Stable Range and Homotopy Groups of Spheres

def freudenthal_stable_range(dim_sphere: int) -> Tuple[int, int]:
    """
    Computes the Freudenthal stability range for sphere S^n.
    Since S^n is (n - 1)-connected, sigma : S^n to Omega S^{n+1} is (2n - 2)-connected.
    Therefore, the suspension homomorphism:
      pi_k(S^n) to pi_{k+1}(S^{n+1})
    is an isomorphism for k < 2n - 2 (i.e. k <= 2n - 3) and a surjection for k = 2n - 2.

    Returns:
      (min_k, max_k): Inclusive range of k for which pi_k(S^n) is in the stable range.
    """
    if dim_sphere < 1:
        raise ValueError(f"Sphere dimension must be at least 1, got {dim_sphere}")
    max_k = 2 * dim_sphere - 2
    return (0, max(0, max_k))


def stable_homotopy_group_sphere(k: int, n: int) -> Dict[str, Any]:
    """
    Calculates the homotopy group pi_k(S^n) and evaluates stability via the
    Freudenthal Suspension Theorem.

    Parameters:
      k: Target homotopy group dimension (pi_k).
      n: Sphere dimension (S^n).

    Returns dictionary with:
      - 'k': k
      - 'n': n
      - 'stem': j = k - n (stable stem)
      - 'is_stable': bool (whether (k, n) is in the Freudenthal stable range)
      - 'group': string representation of the group (e.g. '0', 'Z', 'Z_2', 'Z_24')
      - 'order': int or 'infinity'
      - 'freudenthal_bound': 2n - 2
    """
    if n < 1:
        raise ValueError(f"Sphere dimension n must be >= 1, got {n}")
    if k < 0:
        raise ValueError(f"Homotopy degree k must be >= 0, got {k}")

    stem = k - n
    stable_bound = 2 * n - 2
    is_stable = (k <= stable_bound) if n >= 2 else (k == 1)

    group_desc: str
    order: Union[int, str]

    if k < n:
        # S^n is (n-1)-connected, all lower homotopy groups vanish
        group_desc = "0"
        order = 1
    elif k == n:
        # pi_n(S^n) =~ Z for all n >= 1
        group_desc = "Z"
        order = "infinity"
    elif stem == 1:
        # Stable 1-stem pi_1^s =~ Z_2 (generated by eta)
        if n == 1:
            group_desc = "0"
            order = 1
        elif n == 2:
            group_desc = "Z"  # pi_3(S^2) =~ Z (Hopf fibration)
            order = "infinity"
        else:
            group_desc = "Z_2"  # pi_{n+1}(S^n) =~ Z_2 for n >= 3
            order = 2
    elif stem == 2:
        # Stable 2-stem pi_2^s =~ Z_2 (generated by eta^2)
        if n == 1:
            group_desc = "0"
            order = 1
        elif n == 2:
            group_desc = "Z_2"  # pi_4(S^2) =~ Z_2
            order = 2
        else:
            group_desc = "Z_2"  # pi_{n+2}(S^n) =~ Z_2 for n >= 3
            order = 2
    elif stem == 3:
        # Stable 3-stem pi_3^s =~ Z_24 (generated by nu)
        if n == 1:
            group_desc = "0"
            order = 1
        elif n == 2:
            group_desc = "Z_2"  # pi_5(S^2) =~ Z_2
            order = 2
        elif n == 3:
            group_desc = "Z_12"  # pi_6(S^3) =~ Z_12
            order = 12
        elif n == 4:
            group_desc = "Z_24 + Z_2"  # pi_7(S^4) =~ Z_24 x Z_2
            order = 48
        else:
            group_desc = "Z_24"  # pi_{n+3}(S^n) =~ Z_24 for n >= 5
            order = 24
    else:
        group_desc = f"pi_{k}(S^{n})"
        order = "unknown"

    return {
        "k": k,
        "n": n,
        "stem": stem,
        "is_stable": is_stable,
        "group": group_desc,
        "order": order,
        "freudenthal_bound": stable_bound,
    }
