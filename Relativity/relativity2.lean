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
  lightLike x z ∧ z ≠ x ∧ z ≠ y ∧
  ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := sorry

--axiom axev : ∀ (m k : B), IOb m → IOb k → ∀ (x : R4), ∃ (y : R4), events m x = events k y

theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨hwmkx, hwmky, xney, iob, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, ⟨znex, zney, hwNotExist⟩⟩⟩  := zwExist
    obtain ⟨x', hx'⟩ := axev m k iob iok x
    obtain ⟨y', hy'⟩ := axev m k iob iok y
    obtain ⟨z', hz'⟩ := axev m k iob iok z
    have x'sZero : spatial x' = ![0,0,0] := sorry
    have y'sZero : spatial y' = ![0,0,0] := sorry
    have x'ney' : x' ≠ y' := sorry
    have x'nez' : x' ≠ z' := sorry
    have y'nez' : y' ≠ z' := sorry
    have hx'z'Lightlike : lightLike x' z' := sorry
    have ⟨w', hw'⟩ : ∃ (w' : R4),
      Collinear ℝ {x', z', w'} ∧
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := sorry
    obtain ⟨w, hwEvents⟩ := axev m k iob iok w'
    have hw : lightLike w x ∧ lightLike w y ∧ lightLike w z := sorry
    have hwNot := hwNotExist w
    contradiction
