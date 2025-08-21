import Mathlib
--set_option diagnostics true

abbrev Point4 : Type := Fin 4 → ℝ
abbrev Point3 : Type := Fin 3 → ℝ

-- project 4d point to its spatial components
def point4ToSpace (p : Point4) : Point3 :=
  fun x : Fin 3 =>
    match x with
    | 0 => p 0
    | 1 => p 1
    | 2 => p 2

-- compute the norm of a 3d point
def spaceNormSq (p : Point3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : Point4) : ℝ := spaceNormSq ((point4ToSpace p) - (point4ToSpace q))

axiom B : Type -- Bodies
axiom IB : B → Prop -- Inertial bodies predicate
axiom Ph : B → Prop -- Photon predicate
axiom W : B → B → Point4 → Prop -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : Point4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob m -- Inertial observer predicate
def events (m : B) (x : Point4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set Point4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to send out a light signal in any direction."

def AxPh : Prop := ∀ (m : B), ∀ (x y : Point4), IOb m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = abs (x 3 - y 3) ^2))

axiom axph : AxPh
-- END AXIOM


-- AXIOM 2: "All inertial observers coordinatize the same set of events."
def AxEv : Prop := ∀ (m k : B), IOb m → IOb k → ∀ (x : Point4), ∃ (y : Point4), events m x = events k y

axiom axev : AxEv
-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
def AxSf : Prop := ∀ (m : B), IOb m → ∀ (x : Point4), W m m x → x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0

axiom axsf : AxSf
-- END AXIOM

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

def AxSm : Prop := ∀ (m k : B), IOb m ∧ IOb k → ∀ (x y x' y' : Point4), (x 3 = y 3) ∧ (x' 3 = y' 3) ∧ (events m x = events k x') ∧ (events m y = events k y) → spaceDistanceSq x y = spaceDistanceSq x' y'

axiom axsm : AxSm
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

theorem x_ne_y_evx_ne_evy : ∀ (x y : Point4) (b : B), x ≠ y → events b x ≠ events b y := by
  intro x y b xney events_eq
  let xs : Point3 := point4ToSpace x
  let ys : Point3 := point4ToSpace y
  --by_cases h: ∃ (k : ℝ), k * xs = ys
  sorry


theorem notLightSpeed : ∀ (m k : B), ∀ (x y : Point4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k → ¬ spaceDistanceSq x y = abs (x 3 - y 3) ^ 2 := by
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

  have EVneq1 : events m x ≠ events m y := x_ne_y_evx_ne_evy x y m xney

  have EVneq2 : events k x' ≠ events k y' := by
    rw [← EVmxeqkx']
    rw [← EVmyeqky']
    exact EVneq1
  have x'neqy' : x' ≠ y' := by
    have := x_eq_y_eq_events x' y' k
    by_contra x'eqy'
    have EVkx'eqky' := this x'eqy'
    contradiction

  let x's : Point3 := point4ToSpace x'
  let y's : Point3 := point4ToSpace y'

  have x'sZero : x's = ![0, 0, 0] := by
    have  : W k k x' := by
      rw [← eventsToWorldview]
      rw [← EVmxeqkx']
      rw [eventsToWorldview]
      exact mkx
    have := axsf k iok x' this
    simp [x's]
    unfold point4ToSpace
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
    unfold point4ToSpace
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
      simpa [point4ToSpace] using h
    have hx1 : x' 1 = 0 := by
      have h := congrArg (fun f => f 1) x'sZero
      simpa [point4ToSpace] using h
    have hx2 : x' 2 = 0 := by
      have h := congrArg (fun f => f 2) x'sZero
      simpa [point4ToSpace] using h
    have hy0 : y' 0 = 0 := by
      have h := congrArg (fun f => f 0) y'sZero
      simpa [point4ToSpace] using h
    have hy1 : y' 1 = 0 := by
      have h := congrArg (fun f => f 1) y'sZero
      simpa [point4ToSpace] using h
    have hy2 : y' 2 = 0 := by
      have h := congrArg (fun f => f 2) y'sZero
      simpa [point4ToSpace] using h
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2, hy0, hy1, hy2, x'teqy't]

  contradiction
