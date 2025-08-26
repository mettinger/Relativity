import Relativity.lemmas

open scoped RealInnerProductSpace

theorem zExistsxtneyt : ∀ (x y : R4), spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 → x 3 ≠ y 3 →
            ∃ (z : R4), spaceDistanceSq z x = abs ( z 3 - x 3) ^ 2
            ∧ (z 3 - x 3) ≠ 0
            ∧ z3 = y 3
            ∧ ⟪ spatial z - spatial x, spatial z - spatial y ⟫ = 0 := sorry

theorem zExistsxteqyt : ∀ (x y : R4), spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 → x 3 = y 3 →
            ∃ (z : R4), spaceDistanceSq z x = abs ( z 3 - x 3) ^ 2
            ∧ (z 3 - x 3) ≠ 0
            ∧ ⟪ spatial z - spatial x, spatial y - spatial x ⟫ = 0 := sorry

theorem zExist : ∀ (x y : R4), spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 → ∃ (z : R4),
  ∀ (w : R4), ¬ lightLike w x ∧ lightLike x y ∧ lightLike w z := sorry


theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨hwmkx, hwmky, xney, iob, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, hw⟩ := zwExist
    sorry
