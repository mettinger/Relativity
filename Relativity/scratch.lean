import Mathlib

abbrev Point3 := Fin 3 → ℝ
def test (p q : Point3) : Point3 := p - q
