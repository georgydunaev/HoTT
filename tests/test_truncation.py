"""
Unit tests for Homotopy Fibers, Truncation Levels, and Hedberg's Theorem
"""

import unittest
from hott.identity import HoTTType, IdType, Refl, SymPath
from hott.equivalence import IsContr, IsProp, Equiv, equiv_refl
from hott.truncation import (
    Fiber,
    FiberPoint,
    equiv_to_contr_fibers,
    contr_fibers_to_isequiv,
    TruncIndex,
    MINUS_TWO,
    MINUS_ONE,
    ZERO,
    ONE,
    IsSet,
    IsNType,
    is_contr_to_is_prop,
    is_prop_to_paths_contr,
    is_prop_to_is_set,
    is_contr_to_ntype,
    is_prop_to_ntype,
    is_set_to_ntype,
    ntype_to_is_contr,
    ntype_to_is_prop,
    ntype_to_is_set,
    trunc_succ,
    DecidablePaths,
    WeaklyConstant,
    Collapsible,
    decidable_to_collapsible,
    hedberg_from_collapsible,
    hedberg,
    hedberg_ntype,
)


class TestTruncation(unittest.TestCase):
    def setUp(self):
        self.A = HoTTType("A")
        self.B = HoTTType("B")

    def test_homotopy_fiber_creation(self):
        def f(x):
            return x

        fib = Fiber(f, "y0", self.A, self.A)
        self.assertIn("fib_f(y0)", repr(fib))
        p = Refl(self.A, "y0")
        pt = fib.point("y0", p)
        self.assertEqual(pt.x, "y0")
        self.assertEqual(pt.p, p)
        self.assertEqual(repr(pt), "(y0, refl_y0)")

    def test_equiv_to_contr_fibers(self):
        # Identity equivalence
        e = equiv_refl(self.A)
        contr = equiv_to_contr_fibers(e, "y0")
        self.assertIsInstance(contr, IsContr)
        self.assertEqual(contr.center.x, "y0")
        # Center contraction
        refl_path = contr.contract(contr.center)
        self.assertTrue(refl_path.is_refl())

    def test_contr_fibers_to_isequiv(self):
        def f(x):
            return x

        def contr_fibers(y):
            center = FiberPoint(y, Refl(self.A, y))
            def contr_fn(pt):
                if pt == center:
                    return Refl(HoTTType(f"fib({y})"), center)
                return SymPath("p", HoTTType(f"fib({y})"), center, pt)
            return IsContr(HoTTType(f"fib({y})"), center, contr_fn)

        is_eq = contr_fibers_to_isequiv(f, contr_fibers, self.A, self.A)
        self.assertEqual(is_eq.g("item"), "item")
        self.assertTrue(is_eq.eps("item").is_refl())
        self.assertTrue(is_eq.eta("item").is_refl())

    def test_trunc_index(self):
        t_minus_two = TruncIndex(-2)
        t_minus_one = TruncIndex(-1)
        t_zero = TruncIndex(0)
        t_one = TruncIndex(1)

        self.assertEqual(t_minus_two, MINUS_TWO)
        self.assertEqual(t_minus_one, MINUS_ONE)
        self.assertEqual(t_zero, ZERO)
        self.assertEqual(t_one, ONE)

        self.assertTrue(t_minus_two.is_contr())
        self.assertTrue(t_minus_one.is_prop())
        self.assertTrue(t_zero.is_set())

        self.assertEqual(t_minus_two.succ(), t_minus_one)
        self.assertEqual(t_minus_one.succ(), t_zero)
        self.assertEqual(t_zero.pred(), t_minus_one)

        self.assertTrue(t_minus_two < t_minus_one)
        self.assertTrue(t_minus_one <= t_zero)

        with self.assertRaises(ValueError):
            TruncIndex(-3)

        with self.assertRaises(ValueError):
            t_minus_two.pred()

    def test_is_contr_to_is_prop(self):
        center = "c"
        contr_map = lambda x: Refl(self.A, center) if x == center else SymPath("p", self.A, center, x)
        is_contr = IsContr(self.A, center, contr_map)

        is_prop = is_contr_to_is_prop(is_contr)
        self.assertIsInstance(is_prop, IsProp)
        p_xy = is_prop.path("x1", "x2")
        from hott.identity import Path
        self.assertIsInstance(p_xy, Path)

    def test_is_prop_to_paths_contr_and_is_set(self):
        all_paths = lambda x, y: Refl(self.A, x) if x == y else SymPath("p", self.A, x, y)
        is_prop = IsProp(self.A, all_paths)

        paths_contr = is_prop_to_paths_contr(is_prop, "x1", "x2")
        self.assertIsInstance(paths_contr, IsContr)

        is_set = is_prop_to_is_set(is_prop)
        self.assertIsInstance(is_set, IsSet)

        p = SymPath("p1", self.A, "x1", "x2")
        q = SymPath("p2", self.A, "x1", "x2")
        uip_path = is_set.path2("x1", "x2", p, q)
        self.assertIsNotNone(uip_path)

    def test_is_n_type_hierarchy_and_cumulativity(self):
        center = "c"
        contr_map = lambda x: Refl(self.A, center) if x == center else SymPath("p", self.A, center, x)
        is_contr = IsContr(self.A, center, contr_map)

        # -2 type
        ntype_minus_two = is_contr_to_ntype(is_contr)
        self.assertEqual(ntype_minus_two.n, MINUS_TWO)
        self.assertEqual(ntype_to_is_contr(ntype_minus_two), is_contr)

        # -1 type
        ntype_minus_one = trunc_succ(ntype_minus_two)
        self.assertEqual(ntype_minus_one.n, MINUS_ONE)
        is_prop = ntype_to_is_prop(ntype_minus_one)
        self.assertIsInstance(is_prop, IsProp)

        # 0 type
        ntype_zero = trunc_succ(ntype_minus_one)
        self.assertEqual(ntype_zero.n, ZERO)
        is_set = ntype_to_is_set(ntype_zero)
        self.assertIsInstance(is_set, IsSet)

        # 1 type
        ntype_one = trunc_succ(ntype_zero)
        self.assertEqual(ntype_one.n, ONE)
        sub_zero = ntype_one.path_ntype("x", "y")
        self.assertEqual(sub_zero.n, ZERO)

    def test_hedberg_theorem(self):
        # Type with decidable equality (e.g. Booleans / discrete set)
        Bool = HoTTType("Bool")

        def decide_bool(x, y):
            if x == y:
                return (True, Refl(Bool, x))
            else:
                return (False, f"{x} != {y}")

        dec_paths = DecidablePaths(Bool, decide_bool)
        is_set = hedberg(Bool, dec_paths)
        self.assertIsInstance(is_set, IsSet)

        # Test UIP on true = true
        p1 = Refl(Bool, True)
        p2 = Refl(Bool, True)
        uip_same = is_set.path2(True, True, p1, p2)
        self.assertTrue(uip_same.is_refl())

        p_sym1 = SymPath("p1", Bool, True, True)
        p_sym2 = SymPath("p2", Bool, True, True)
        uip_diff = is_set.path2(True, True, p_sym1, p_sym2)
        self.assertIsNotNone(uip_diff)

        # Test hedberg_ntype
        ntype_bool = hedberg_ntype(Bool, dec_paths)
        self.assertEqual(ntype_bool.n, ZERO)


if __name__ == "__main__":
    unittest.main()
