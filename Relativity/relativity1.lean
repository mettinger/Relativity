import Mathlib
--set_option diagnostics true

abbrev Point4 : Type := Fin 4 → ℝ
abbrev Point3 : Type := Fin 3 → ℝ

-- project 4d point to its spatial components
def spatial (p : Point4) : Point3 :=
  fun x : Fin 3 =>
    match x with
    | 0 => p 0
    | 1 => p 1
    | 2 => p 2

-- compute the norm of a 3d point
def spaceNormSq (p : Point3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : Point4) : ℝ := spaceNormSq ((spatial p) - (spatial q))

axiom B : Type -- Bodies
axiom IB : B → Prop -- Inertial bodies predicate
axiom Ph : B → Prop -- Photon predicate
axiom W : B → B → Point4 → Prop -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : Point4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob m -- Inertial observer predicate
def events (m : B) (x : Point4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set Point4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to send out a light signal in any direction."

axiom axph : ∀ (m : B), ∀ (x y : Point4), IOb m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = abs (x 3 - y 3) ^2))

-- END AXIOM

-- AXIOM 2: "All inertial observers coordinatize the same set of events."
axiom axev : ∀ (m k : B), IOb m → IOb k → ∀ (x : Point4), ∃ (y : Point4), events m x = events k y

-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
axiom axsf : ∀ (m : B), IOb m → ∀ (x : Point4), W m m x → x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0

-- END AXIOM

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

axiom axsm : ∀ (m k : B), IOb m ∧ IOb k → ∀ (x y x' y' : Point4), (x 3 = y 3) ∧ (x' 3 = y' 3) ∧ (events m x = events k x') ∧ (events m y = events k y) → spaceDistanceSq x y = spaceDistanceSq x' y'

-- END AXIOM

--------------------------------------------

theorem eventsToWorldview : ∀ (b ob : B), ∀ (x : Point4), b ∈ events ob x ↔ W ob b x := by
  intro b ob x
  rw [events]
  simp

theorem x_eq_y_eq_events : ∀ (x y : Point4), ∀ (ob : B), x = y → events ob x = events ob y := by
  intro x y ob xeqy
  ext ob
  unfold events
  simp
  rw [xeqy]

theorem oppDirection : ∀ (m : B) (x y : Point4), IOb m → y 3 > x 3 →
  spaceDistanceSq x y = abs (y 3 - x 3) ^ 2 → ∃ (p : B), Ph p ∧ W m p x ∧ ¬ W m p y := by
    intro m x y iom ytgtxt onLightcone
    let yOpp : Point4 :=
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


theorem sp_tm_eq_eq : ∀ (x y: Point4), spaceDistanceSq x y = 0 → x 3 = y 3 → x = y := by
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

theorem spaceDistComm : ∀ (x y: Point4), spaceDistanceSq x y = spaceDistanceSq y x := by
  intro x y
  unfold spaceDistanceSq
  unfold spatial
  unfold spaceNormSq
  simp
  ring

theorem x_ne_y_evx_ne_evy : ∀ (x y : Point4) (b : B), IOb b → x ≠ y → events b x ≠ events b y := by
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


theorem notLightSpeed : ∀ (m k : B), ∀ (x y : Point4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
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
      have := x_eq_y_eq_events x' y' k
      by_contra x'eqy'
      have EVkx'eqky' := this x'eqy'
      contradiction

    let x's : Point3 := spatial x'
    let y's : Point3 := spatial y'

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
