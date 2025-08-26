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
  lightLike x z ∧ x ≠ z ∧ y ≠ z ∧
  ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := sorry

--axiom axev : ∀ (m k : B), IOb m → IOb k → ∀ (x : R4), ∃ (y : R4), events m x = events k y

theorem x_ne_y_imp_x'_ne_y' : ∀ (x y x' y': R4), x ≠ y →
  ∀ (m k : B), IOb m → IOb k → events m x = events k x' → events m y = events k y' → x' ≠ y' := by
    intro x y x' y' hxney m k iom _ hxx'EventsEq hyy'EventsEq hx'eqy'
    rw [← hx'eqy'] at hyy'EventsEq
    rw [← hyy'EventsEq] at hxx'EventsEq
    have hxx'EventsNotEq := x_ne_y_evx_ne_evy x y m iom hxney
    exact hxx'EventsNotEq hxx'EventsEq

theorem lightLikeImplightLike: ∀ (x y x' y' : R4), ∀ (m k : B), IOb m → IOb k →
  lightLike x y → events m x = events k x' -> events m y = events k y' → lightLike x' y' := by
    intro x y x' y' m k iom iok hllxy hxx'EventsEq hyy'EventsEq


theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨hwmkx, hwmky, xney, iom, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, ⟨xnez, ynez, hwNotExist⟩⟩⟩  := zwExist
    obtain ⟨x', hx'⟩ := axev m k iom iok x
    obtain ⟨y', hy'⟩ := axev m k iom iok y
    obtain ⟨z', hz'⟩ := axev m k iom iok z
    have x'sZero : spatial x' = ![0,0,0] := by
      have wkkx' : W k k x' := by
        apply (eventsToWorldview k k x').mp
        rw [← hx']
        apply (eventsToWorldview k m x).mpr
        assumption
      have hx's000 := axsf k iok x' wkkx'
      simp [hx's000]
      unfold spatial
      ext i
      aesop
    have y'sZero : spatial y' = ![0,0,0] := by
      have wkky' : W k k y' := by
        apply (eventsToWorldview k k y').mp
        rw [← hy']
        apply (eventsToWorldview k m y).mpr
        assumption
      have hy's000 := axsf k iok y' wkky'
      simp [hy's000]
      unfold spatial
      ext i
      aesop
    have x'ney' : x' ≠ y' := x_ne_y_imp_x'_ne_y' x y x' y' xney m k iom iok hx' hy'
    have x'nez' : x' ≠ z' := x_ne_y_imp_x'_ne_y' x z x' z' xnez m k iom iok hx' hz'
    have y'nez' : y' ≠ z' := x_ne_y_imp_x'_ne_y' y z y' z' ynez m k iom iok hy' hz'
    have hx'z'Lightlike : lightLike x' z' := lightLikeImplightLike x z x' z' m k iom iok hxzLightlike hx' hz'
    have ⟨w', ⟨hcollinearx'z'w', hllw'x', hllw'y', hllw'z'⟩⟩ : ∃ (w' : R4),
      Collinear ℝ {x', z', w'} ∧
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := sorry
    obtain ⟨w, hwEvents⟩  := axev k m iok iom w'
    have hw : lightLike w x ∧ lightLike w y ∧ lightLike w z := by
      constructor
      case left := lightLikeImplightLike w' x' w x k m iok iom hllw'x' hwEvents hx'.symm
      case right := by
        constructor
        case left := lightLikeImplightLike w' y' w y k m iok iom hllw'y' hwEvents hy'.symm
        case right := lightLikeImplightLike w' z' w z k m iok iom hllw'z' hwEvents hz'.symm
    have hwNot := hwNotExist w
    contradiction
