import Mathlib

--set_option diagnostics true

-- 4 dimensional point
@[ext]
structure Point4 where
  x : ℝ
  y : ℝ
  z : ℝ
  t : ℝ

-- spatial projection of 4d point
@[ext]
structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

-- project 4d point to its spatial components
def point4ToSpace (p : Point4) : Point3 := Point3.mk p.x p.y p.z

-- compute distance between two 3d points
def pointSpaceMinus (p q: Point3): Point3 := Point3.mk (p.x - q.x) (p.y - q.y) (p.z - q.z)

-- compute the norm of a 3d point
def spaceNormSq (p : Point3) : ℝ := p.x ^ 2 + p.y ^ 2 + p.z ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : Point4) : ℝ := spaceNormSq (pointSpaceMinus (point4ToSpace p) (point4ToSpace q))

def origin4 : Point4 where
  x := 0
  y := 0
  z := 0
  t := 0

def xLightYear4 : Point4 where
  x := 1
  y := 0
  z := 0
  t := 1

axiom B : Type -- Bodies
axiom IB : B → Prop -- Inertial bodies predicate
axiom Ph : B → Prop -- Photon predicate
axiom W : B → B → Point4 → Prop -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : Point4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob m -- Inertial observer predicate
def events (m : B) (x : Point4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set Point4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is the same everywhere and in every direction, and it is finite. Furthermore, it is possible to send out a light signal in any direction."

def AxPh : Prop := ∀ (m : B), ∀ (x y : Point4), IOb m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = abs (x.t - y.t) ^2))

axiom axph : AxPh
-- END AXIOM


-- AXIOM 2: "All inertial observers coordinatize the same set of events."
def AxEv : Prop := ∀ (m k : B), IOb m → IOb k → ∀ (x : Point4), ∃ (y : Point4), events m x = events k y

axiom axev : AxEv
-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
def AxSf : Prop := ∀ (m : B), IOb m → ∀ (x : Point4), W m m x → x.x = 0 ∧ x.y = 0 ∧ x.z = 0

axiom axsf : AxSf
-- END AXIOM

-- AXIOM 4a : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

def AxSm : Prop := ∀ (m k : B), IOb m ∧ IOb k → ∀ (x y x' y' : Point4), (x.t = y.t) ∧ (x'.t = y'.t) ∧ (events m x = events k x') ∧ (events m y = events k y) → spaceDistanceSq x y = spaceDistanceSq x' y'

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

theorem x_ne_y_evx_ne_evy : ∀ (x y : Point4) (b : B), x ≠ y → events b x ≠ events b y := sorry

theorem notLightSpeed : ∀ (m k : B), ∀ (x y : Point4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k → ¬ spaceDistanceSq x y = abs (x.t - y.t) ^ 2 := by
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

  have x'sZero : x's = Point3.mk 0 0 0 := by
    have  : W k k x' := by
      rw [← eventsToWorldview]
      rw [← EVmxeqkx']
      rw [eventsToWorldview]
      exact mkx
    have := axsf k iok x' this
    simp [x's]
    unfold point4ToSpace
    simp
    exact this

  have y'sZero : y's = Point3.mk 0 0 0 := by
    have  : W k k y' := by
      rw [← eventsToWorldview]
      rw [← EVmyeqky']
      rw [eventsToWorldview]
      exact mky
    have := axsf k iok y' this
    simp [y's]
    unfold point4ToSpace
    simp
    exact this


  have x'teqy't : x'.t = y'.t := by
    #check eq_of_abs_sub_eq_zero
    sorry

  have x'eqy' : x' = y' := by
    ext
    case t := x'teqy't
    case x := by
      have x's.xZero : x's.x = 0 := by
        rw [x'sZero]
      have y's.xZero : y's.x = 0 := by
        rw [y'sZero]
      rw [show x'.x = x's.x from rfl]
      rw [show y'.x = y's.x from rfl]
      rw [x'sZero, y'sZero]
    case y := by
      have x's.xZero : x's.y = 0 := by
        rw [x'sZero]
      have y's.xZero : y's.y = 0 := by
        rw [y'sZero]
      rw [show x'.y = x's.y from rfl]
      rw [show y'.y = y's.y from rfl]
      rw [x'sZero, y'sZero]
    case z := by
      have x's.xZero : x's.z = 0 := by
        rw [x'sZero]
      have y's.xZero : y's.z = 0 := by
        rw [y'sZero]
      rw [show x'.z = x's.z from rfl]
      rw [show y'.z = y's.z from rfl]
      rw [x'sZero, y'sZero]
  contradiction


#exit
-- AXIOM 4b : "the speed of light is 1 for all inertial observers."
--def AxSmB : Prop := ∀ (m : B), IOb m → ∃ (p : B), Ph p ∧ W m p origin4 ∧ W m p xLightYear4

--axiom axsmb : AxSmB
-- END AXIOM
