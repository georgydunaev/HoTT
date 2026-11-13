"""
Unit tests for HoTT Identity Types, J-Eliminator, and Path Groupoids
"""

import unittest
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


class TestIdentity(unittest.TestCase):
    def setUp(self):
        self.A = HoTTType("A")
        self.x = "x"
        self.y = "y"
        self.z = "z"
        self.w = "w"

    def test_refl_and_id_type(self):
        id_xx = IdType(self.A, self.x, self.x)
        refl_x = Refl(self.A, self.x)
        self.assertEqual(refl_x.type, id_xx)
        self.assertTrue(refl_x.is_refl())
        self.assertEqual(refl_x.source, self.x)
        self.assertEqual(refl_x.target, self.x)

    def test_j_elim_refl_computation_rule(self):
        """Computation rule: J(C, c, x, x, refl_x) = c(x)."""
        refl_x = Refl(self.A, self.x)

        def C(a, b, p):
            return HoTTType(f"C({a}, {b})")

        def c(a):
            return f"base_witness_{a}"

        res = j_elim(C, c, self.x, self.x, refl_x)
        self.assertEqual(res, "base_witness_x")

    def test_j_paulin_mohring(self):
        """Paulin-Mohring based path induction."""
        refl_x = Refl(self.A, self.x)

        def C(b, p):
            return HoTTType(f"C({b})")

        base_val = "witness_base"
        res = j_paulin_mohring(self.x, C, base_val, self.x, refl_x)
        self.assertEqual(res, base_val)

    def test_path_concat_and_units(self):
        p = SymPath("p", self.A, self.x, self.y)
        refl_x = Refl(self.A, self.x)
        refl_y = Refl(self.A, self.y)

        # Left unit law: refl_x . p = p
        left = concat(refl_x, p)
        self.assertEqual(left, p)
        lu_prf = left_unit(p)
        self.assertTrue(lu_prf.is_refl())

        # Right unit law: p . refl_y = p
        right = concat(p, refl_y)
        self.assertEqual(right, p)
        ru_prf = right_unit(p)
        self.assertTrue(ru_prf.is_refl())

    def test_path_associativity(self):
        p = SymPath("p", self.A, self.x, self.y)
        q = SymPath("q", self.A, self.y, self.z)
        r = SymPath("r", self.A, self.z, self.w)

        assoc_pqr = assoc(p, q, r)
        self.assertEqual(assoc_pqr.A, IdType(self.A, self.x, self.w))

        # In pure refl case, associativity holds definitionally
        rx = Refl(self.A, self.x)
        ry = Refl(self.A, self.x)
        rz = Refl(self.A, self.x)
        self.assertTrue(assoc(rx, ry, rz).is_refl())

    def test_path_inverses(self):
        p = SymPath("p", self.A, self.x, self.y)
        p_inv = inverse(p)
        self.assertEqual(p_inv.source, self.y)
        self.assertEqual(p_inv.target, self.x)

        # Inversion of inversion
        p_inv_inv = inverse(p_inv)
        self.assertEqual(p_inv_inv, p)
        self.assertTrue(inv_inv(p).is_refl())

        # Left and right inverses on refl
        refl_x = Refl(self.A, self.x)
        self.assertTrue(left_inverse(refl_x).is_refl())
        self.assertTrue(right_inverse(refl_x).is_refl())

    def test_inv_concat(self):
        p = SymPath("p", self.A, self.x, self.y)
        q = SymPath("q", self.A, self.y, self.z)
        inv_comp = inv_concat(p, q)
        self.assertEqual(inv_comp.A, IdType(self.A, self.z, self.x))

    def test_transport(self):
        P = lambda a: HoTTType(f"P({a})")
        refl_x = Refl(self.A, self.x)
        u = "witness_u"
        self.assertEqual(transport(P, refl_x, u), u)

    def test_ap(self):
        f = lambda a: f"f({a})"
        refl_x = Refl(self.A, self.x)
        ap_refl = ap(f, refl_x)
        self.assertTrue(ap_refl.is_refl())
        self.assertEqual(ap_refl.source, "f(x)")


if __name__ == "__main__":
    unittest.main()
