"""
Unit tests for Homotopy Fibers, Contractible Types, and Equivalences
"""

import unittest
from hott.identity import HoTTType, IdType, Refl, SymPath
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


class TestEquivalence(unittest.TestCase):
    def setUp(self):
        self.A = HoTTType("A")
        self.B = HoTTType("B")
        self.C = HoTTType("C")

    def test_homotopy_creation(self):
        f = lambda x: x
        g = lambda x: x
        H_map = lambda x: Refl(self.A, x)
        H = Homotopy(f, g, H_map, self.A, self.A)
        self.assertTrue(H("a").is_refl())

    def test_contractible_type(self):
        center = "c"
        contr_map = lambda x: Refl(self.A, center) if x == center else SymPath("p", self.A, center, x)
        is_contr = IsContr(self.A, center, contr_map)
        self.assertEqual(is_contr.center, center)
        self.assertTrue(is_contr.contract("c").is_refl())

    def test_qinv_and_isequiv(self):
        f = lambda x: x
        g = lambda x: x
        H_eta = lambda x: Refl(self.A, x)
        H_eps = lambda y: Refl(self.A, y)
        eta = Homotopy(f, f, H_eta, self.A, self.A)
        eps = Homotopy(g, g, H_eps, self.A, self.A)

        q = QInv(f, g, eta, eps, self.A, self.A)
        is_eq = qinv_to_isequiv(q)
        self.assertIsInstance(is_eq, IsEquiv)
        self.assertIsNotNone(is_eq.tau)

        # Fiber contractibility
        fib_contr = is_eq.fiber_contractible("a")
        self.assertIsInstance(fib_contr, IsContr)

    def test_is_prop_isequiv(self):
        f = lambda x: x
        prop_witness = is_prop_isequiv(f, self.A, self.A)
        self.assertIsInstance(prop_witness, IsProp)

    def test_equiv_relations(self):
        # Reflexivity
        e_refl = equiv_refl(self.A)
        self.assertEqual(e_refl.A, self.A)
        self.assertEqual(e_refl.B, self.A)
        self.assertEqual(e_refl("item"), "item")
        self.assertEqual(e_refl.inv("item"), "item")

        # Symmetry
        e_symm = equiv_symm(e_refl)
        self.assertEqual(e_symm.A, self.A)
        self.assertEqual(e_symm.B, self.A)

        # Transitivity
        e_trans = equiv_trans(e_refl, e_symm)
        self.assertEqual(e_trans.A, self.A)
        self.assertEqual(e_trans.B, self.A)
        self.assertEqual(e_trans("test"), "test")


if __name__ == "__main__":
    unittest.main()
