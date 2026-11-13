"""
HoTT: Homotopy Type Theory Core Package

Exports:
- Identity Types, J-Eliminator, Path Groupoids
- Homotopy Fibers, Contractible Types, Equivalences
- Voevodsky's Univalence Axiom and Function Extensionality
"""

from hott.identity import (
    HoTTType,
    IdType,
    Path,
    Refl,
    SymPath,
    ConcatPath,
    InversePath,
    j_elim,
    j_paulin_mohring,
    concat,
    inverse,
    transport,
    ap,
    left_unit,
    right_unit,
    assoc,
    left_inverse,
    right_inverse,
    inv_inv,
    inv_concat,
)

from hott.equivalence import (
    Homotopy,
    FiberPoint,
    IsContr,
    IsProp,
    QInv,
    IsEquiv,
    Equiv,
    qinv_to_isequiv,
    is_prop_isequiv,
    equiv_refl,
    equiv_symm,
    equiv_trans,
)

from hott.univalence import (
    Universe,
    UNIVERSE_0,
    id_to_eqv,
    UnivalenceAxiom,
    happly,
    FunctionExtensionality,
)

__all__ = [
    "HoTTType",
    "IdType",
    "Path",
    "Refl",
    "SymPath",
    "ConcatPath",
    "InversePath",
    "j_elim",
    "j_paulin_mohring",
    "concat",
    "inverse",
    "transport",
    "ap",
    "left_unit",
    "right_unit",
    "assoc",
    "left_inverse",
    "right_inverse",
    "inv_inv",
    "inv_concat",
    "Homotopy",
    "FiberPoint",
    "IsContr",
    "IsProp",
    "QInv",
    "IsEquiv",
    "Equiv",
    "qinv_to_isequiv",
    "is_prop_isequiv",
    "equiv_refl",
    "equiv_symm",
    "equiv_trans",
    "Universe",
    "UNIVERSE_0",
    "id_to_eqv",
    "UnivalenceAxiom",
    "happly",
    "FunctionExtensionality",
]
