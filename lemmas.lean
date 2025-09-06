import Relativity.definitions

theorem oppDirection : ∀ (m : B) (x y : R4), IOb m → y 3 > x 3 →
  lightLike x y → ∃ (p : B), Ph p ∧ W m p x ∧ ¬ W m p y := by sorry
  /-
    intro m x y iom ytgtxt onLightcone
    let yOpp : R4 :=
      fun n : Fin 4 =>
      match n with
      | 0 => (x 0) - (y 0 - x 0)
      | 1 => (x 1) - (y 1 - x 1)
      | 2 => (x 2) - (y 2 - x 2)
      | 3 => y 3

    have h0 := (axph m x yOpp iom).mpr
    have sDistyyOppEq : spaceDistanceSq x y = spaceDistanceSq x yOpp := by
      unfold spaceDistanceSq
      unfold spatial
      unfold spaceNormSq
      simp [yOpp]
      ring
    rw [sDistyyOppEq] at onLightcone
    have : y 3 = yOpp 3 := rfl
    rw [this] at onLightcone
    rw [abs_sub_comm] at onLightcone
    have h0 := h0 onLightcone
    obtain ⟨p, hp, hwmpx, hmpyopp⟩ := h0
    use p
    constructor
    exact hp
    constructor
    exact hwmpx

    intro wmpy
    have sd_y_yOpp := (axph m y yOpp iom).1 ⟨p, hp, wmpy, hmpyopp⟩
    have sd_y_yOpp_zero : spaceDistanceSq y yOpp = 0 := by
      simpa [yOpp] using sd_y_yOpp
    have calcDist : spaceDistanceSq y yOpp = 4 * spaceDistanceSq x y := by
      unfold spaceDistanceSq
      unfold spatial
      unfold spaceNormSq
      simp [yOpp]
      ring
    have sxy_zero : spaceDistanceSq x y = 0 := by
      have h : 4 * spaceDistanceSq x y = 0 := by
        simpa [calcDist] using sd_y_yOpp_zero
      have h4 : (4:ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left h4
    --have pos_time : 0 < y 3 - x 3 := sub_pos.mpr ytgtxt
    --have abs_eq : abs (y 3 - x 3) = y 3 - x 3 := abs_of_pos pos_time
    have hsq : (y 3 - x 3) ^ 2 = 0 := by
      have onL := onLightcone
      rw [← this] at onL
      rw [← sq_abs]
      rw [abs_sub_comm]
      have yyOppSpaceDist : spaceDistanceSq x y = spaceDistanceSq x yOpp := by
        unfold spaceDistanceSq
        unfold spatial
        unfold spaceNormSq
        simp
        ring
      rw [← yyOppSpaceDist, sxy_zero] at onL
      exact onL.symm
    have htime_eq : y 3 - x 3 = 0 := (sq_eq_zero_iff).1 hsq
    have hyeqxtime : y 3 = x 3 := sub_eq_zero.mp htime_eq
    exact (ne_of_gt ytgtxt) hyeqxtime

-/
theorem x_ne_y_evx_ne_evy : ∀ (x y : R4) (b : B), IOb b → x ≠ y → events b x ≠ events b y := by sorry

theorem x_ne_y_imp_x'_ne_y' : ∀ (x y x' y': R4), x ≠ y →
  ∀ (m k : B), IOb m → IOb k → events m x = events k x' → events m y = events k y' → x' ≠ y' := by
    intro x y x' y' hxney m k iom _ hxx'EventsEq hyy'EventsEq hx'eqy'
    rw [← hx'eqy'] at hyy'EventsEq
    rw [← hyy'EventsEq] at hxx'EventsEq
    have hxx'EventsNotEq := x_ne_y_evx_ne_evy x y m iom hxney
    exact hxx'EventsNotEq hxx'EventsEq

/-
theorem x_ne_y_evx_ne_evy : ∀ (x y : R4) (b : B), IOb b → x ≠ y → events b x ≠ events b y := by
  intro x y b iobb xney events_eq
  by_cases spatialDistance : spaceDistanceSq x y = abs (x 3 - y 3) ^ 2
  case neg =>
    have photonExists : ∃ (p : B), Ph p ∧ W b p x := by
      have h := (axph b x x iobb).2
      simp at h
      unfold spaceDistanceSq at h
      simp at h
      unfold spaceNormSq at h
      simp at h
      exact h
    have photonNotExists : ∀ (p : B), Ph p → W b p x → ¬ W b p y := by
      intro p hp hwbpx hwpby
      have h := (axph b x y iobb).1 ⟨p, hp, hwbpx, hwpby⟩
      contradiction
    obtain ⟨p, ⟨hp1, hp2⟩⟩ := photonExists
    have h : p ∈ events b x := (eventsToWorldview p b x).mpr hp2
    have h' : p ∈ events b y := by
      simpa [events_eq] using h
    have hp3 : W b p y := (eventsToWorldview p b y).mp h'
    have hny : ¬ W b p y := photonNotExists p hp1 hp2
    exact hny hp3

  case pos =>
    cases lt_trichotomy (x 3) (y 3)
    case inl =>
      rename_i xtltyt
      rw [abs_sub_comm] at spatialDistance
      have ⟨p, _, hwbpx, hnwbpy⟩ := oppDirection b x y iobb xtltyt spatialDistance
      have h : W b p y := by
        have pEVbx : p ∈ events b x := (eventsToWorldview p b x).mpr hwbpx
        have pEVby : p ∈ events b y := by simpa [events_eq] using pEVbx
        exact (eventsToWorldview p b y).mp pEVby
      exact hnwbpy h
    case inr =>
      rename_i temp
      obtain xteqyt|ytltxt := temp
      case inl =>
        rw [xteqyt] at spatialDistance
        simp at spatialDistance
        have xeqy : x = y := sp_tm_eq_eq x y spatialDistance xteqyt
        contradiction
      case inr =>
        rw [spaceDistComm] at spatialDistance
        have ⟨p, _, hwbpy, hnwbpx⟩ := oppDirection b y x iobb ytltxt spatialDistance
        have h : W b p x := by
          have pEVby : p ∈ events b y := (eventsToWorldview p b y).mpr hwbpy
          have pEVbx : p ∈ events b x := by simpa [events_eq] using pEVby
          exact (eventsToWorldview p b x).mp pEVbx
        exact hnwbpx h
-/
