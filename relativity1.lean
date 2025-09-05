import relativity.lemmas

theorem notLightSpeed : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y = abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨mkx, mky, xney, iom, iok⟩ lightSpeed
    have  ⟨p, ⟨pph, mpx, mpy⟩⟩ : ∃ p, Ph p ∧ W m p x ∧ W m p y := (axph m x y iom).mpr lightSpeed
    have pEVmx : p ∈ events m x := by
      rw [events]
      exact mpx
    have pEVmy : p ∈ events m y := by
      rw [events]
      exact mpy
    have ⟨x', EVmxeqkx'⟩ := axev m k iom iok x
    have ⟨y', EVmyeqky'⟩ := axev m k iom iok y

    have EVneq1 : events m x ≠ events m y := x_ne_y_evx_ne_evy x y m iom xney

    have EVneq2 : events k x' ≠ events k y' := by
      rw [← EVmxeqkx']
      rw [← EVmyeqky']
      exact EVneq1
    have x'neqy' : x' ≠ y' := by
      by_contra x'eqy'
      rw [x'eqy'] at EVneq2
      contradiction

    let x's : R3 := spatial x'
    let y's : R3 := spatial y'

    have x'sZero : x's = ![0, 0, 0] := by
      have  : W k k x' := by
        rw [← eventsToWorldview]
        rw [← EVmxeqkx']
        rw [eventsToWorldview]
        exact mkx
      have := axsf k iok x' this
      simp [x's]
      unfold spatial
      simp
      simp [this]
      aesop

    have y'sZero : y's = ![0, 0, 0] := by
      have  : W k k y' := by
        rw [← eventsToWorldview]
        rw [← EVmyeqky']
        rw [eventsToWorldview]
        exact mky
      have := axsf k iok y' this
      simp [y's]
      unfold spatial
      simp
      simp [this]
      aesop

    have spacedistSqx'y'0 : spaceDistanceSq x' y' = 0 := by
      unfold spaceDistanceSq
      change spaceNormSq (x's - y's) = 0
      rw [x'sZero, y'sZero]
      simp
      unfold spaceNormSq
      simp

    have x'teqy't : x' 3 = y' 3 := by
      have pEVkx' : p ∈ events k x' := by
        rw [← EVmxeqkx']
        exact pEVmx
      have pEVky' : p ∈ events k y' := by
        rw [← EVmyeqky']
        exact pEVmy
      have pWkx' : W k p x' := (eventsToWorldview p k x').mp pEVkx'
      have pWky' : W k p y' := (eventsToWorldview p k y').mp pEVky'
      have photon_k : ∃ p₀, Ph p₀ ∧ W k p₀ x' ∧ W k p₀ y' := ⟨p, pph, pWkx', pWky'⟩
      have lightspeed_k : spaceDistanceSq x' y' = abs (x' 3 - y' 3) ^ 2 :=
        (axph k x' y' iok).mp photon_k
      have h0 : 0 = abs (x' 3 - y' 3) ^ 2 :=
        Eq.trans spacedistSqx'y'0.symm lightspeed_k
      have habs0 : abs (x' 3 - y' 3) ^ 2 = 0 := h0.symm
      have habs : abs (x' 3 - y' 3) = 0 := by
        have : abs (x' 3 - y' 3) * abs (x' 3 - y' 3) = 0 := by
          simpa [pow_two] using habs0
        exact mul_self_eq_zero.mp this
      have diff0 : x' 3 - y' 3 = 0 := abs_eq_zero.mp habs
      exact sub_eq_zero.mp diff0

    have x'eqy' : x' = y' := by
      have hx0 : x' 0 = 0 := by
        have h := congrArg (fun f => f 0) x'sZero
        simpa [spatial] using h
      have hx1 : x' 1 = 0 := by
        have h := congrArg (fun f => f 1) x'sZero
        simpa [spatial] using h
      have hx2 : x' 2 = 0 := by
        have h := congrArg (fun f => f 2) x'sZero
        simpa [spatial] using h
      have hy0 : y' 0 = 0 := by
        have h := congrArg (fun f => f 0) y'sZero
        simpa [spatial] using h
      have hy1 : y' 1 = 0 := by
        have h := congrArg (fun f => f 1) y'sZero
        simpa [spatial] using h
      have hy2 : y' 2 = 0 := by
        have h := congrArg (fun f => f 2) y'sZero
        simpa [spatial] using h
      ext i
      fin_cases i <;> simp [hx0, hx1, hx2, hy0, hy1, hy2, x'teqy't]

    contradiction
