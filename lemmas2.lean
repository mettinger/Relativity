import Relativity.definitions

theorem norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

theorem norm_sq_is_sum_of_squares : ∀ (v : R3), (v 0)^2 + (v 1)^2 + (v 2)^2 = (norm v) ^ 2 := by
  intro v
  rw [EuclideanSpace.norm_sq_eq]
  norm_num
  have hcoords :
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = ∑ x : Fin 3, (v x) ^ 2 := by
    simpa using
      (Fin.sum_univ_three (fun x : Fin 3 => (v x) ^ 2)).symm
  exact hcoords

theorem spatialDiff : ∀ (x y : R4), spatial x - spatial y = ![x 0 - y 0, x 1 - y 1, x 2 - y 2] := by
  intro x y
  unfold spatial
  aesop
theorem eventsToWorldview : ∀ (b ob : B), ∀ (x : R4), b ∈ events ob x ↔ W ob b x := by
  intro b ob x
  rw [events]
  simp

theorem timeDistanceComm : ∀ (x y : R4), timeDistanceSq x y = timeDistanceSq y x := by
  intro x y
  unfold timeDistanceSq
  ring

theorem spaceDistanceComm : ∀ (x y: R4), spaceDistanceSq x y = spaceDistanceSq y x := by
  intro x y
  unfold spaceDistanceSq
  unfold spatial
  unfold spaceNormSq
  simp
  ring

theorem lightLikeSymm : ∀ (x y : R4), lightLike x y → lightLike y x := by
  intro x y hllxy
  unfold lightLike at *
  rw [← spaceDistanceComm x y]
  rw [← timeDistanceComm x y]
  assumption

theorem lightLikeImplightLike: ∀ (x y x' y' : R4), ∀ (m k : B), IOb m → IOb k →
  lightLike x y → events m x = events k x' -> events m y = events k y' → lightLike x' y' := by
    intro x y x' y' m k iom iok hllxy hxx'EventsEq hyy'EventsEq
    unfold lightLike at *
    obtain ⟨p, hp, hwmpx, hwmpy⟩ := (axph m x y iom).mpr hllxy
    have hwkpx' : W k p x' := by
      have hpInEvmx := (eventsToWorldview p m x).mpr hwmpx
      rw [hxx'EventsEq] at hpInEvmx
      exact (eventsToWorldview p k x').mp hpInEvmx
    have hwkpy' : W k p y' := by
      have hpInEvmy := (eventsToWorldview p m y).mpr hwmpy
      rw [hyy'EventsEq] at hpInEvmy
      exact (eventsToWorldview p k y').mp hpInEvmy
    exact (axph k x' y' iok).mp ⟨p, ⟨hp, hwkpx', hwkpy'⟩⟩

theorem sp_tm_eq_eq : ∀ (x y: R4), spaceDistanceSq x y = 0 → x 3 = y 3 → x = y := by
  intro x y hsp htime
  have hsum := hsp
  unfold spaceDistanceSq at hsum
  unfold spatial at hsum
  unfold spaceNormSq at hsum
  simp at hsum
  -- Now hsum : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = 0
  -- Derive each spatial coordinate equal
  have hx0sq : (x 0 - y 0) ^ 2 = 0 := by
    have heq : (x 0 - y 0) ^ 2 = - ((x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) := by
      linarith [hsum]
    have a_nonpos : (x 0 - y 0) ^ 2 ≤ 0 := by
      have : 0 ≤ (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : - ((x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) ≤ 0 := by linarith
      simpa [heq]
    exact le_antisymm a_nonpos (sq_nonneg _)
  have hx1sq : (x 1 - y 1) ^ 2 = 0 := by
    have heq : (x 1 - y 1) ^ 2 = - ((x 0 - y 0) ^ 2 + (x 2 - y 2) ^ 2) := by
      linarith [hsum]
    have a_nonpos : (x 1 - y 1) ^ 2 ≤ 0 := by
      have : 0 ≤ (x 0 - y 0) ^ 2 + (x 2 - y 2) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : - ((x 0 - y 0) ^ 2 + (x 2 - y 2) ^ 2) ≤ 0 := by linarith
      simpa [heq]
    exact le_antisymm a_nonpos (sq_nonneg _)
  have hx2sq : (x 2 - y 2) ^ 2 = 0 := by
    have heq : (x 2 - y 2) ^ 2 = - ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
      linarith [hsum]
    have a_nonpos : (x 2 - y 2) ^ 2 ≤ 0 := by
      have : 0 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : - ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) ≤ 0 := by linarith
      simpa [heq]
    exact le_antisymm a_nonpos (sq_nonneg _)
  have hx0 : x 0 = y 0 := by
    have := (sq_eq_zero_iff).1 hx0sq
    simpa [sub_eq_zero] using this
  have hx1 : x 1 = y 1 := by
    have := (sq_eq_zero_iff).1 hx1sq
    simpa [sub_eq_zero] using this
  have hx2 : x 2 = y 2 := by
    have := (sq_eq_zero_iff).1 hx2sq
    simpa [sub_eq_zero] using this
  ext i ; fin_cases i <;> simp [hx0, hx1, hx2, htime]
