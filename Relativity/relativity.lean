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
noncomputable def spaceNorm (p : Point3) : ℝ := Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)

-- compute the spatial distance between to 4d points
noncomputable def spaceDistance (p q : Point4) : ℝ := spaceNorm (pointSpaceMinus (point4ToSpace p) (point4ToSpace q))

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
axiom m : B

def Ob (m : B) : Prop := ∃ (b : B) (pt : Point4 ) , W m b pt -- Observer predicate

def IOb (m : B) : Prop := IB m ∧ Ob m -- Inertial observer predicate

def events (m : B) (x : Point4) : Set B := { b | W m b x } -- events observed by m at x

def wl (m b : B) : Set Point4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is the same everywhere and in every direction, and it is finite. Furthermore, it is possible to send out a light signal in any direction."

def AxPh : Prop := ∀ (m : B), ∀ (x y : Point4), IOb m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistance x y = abs (x.t - y.t)))

axiom axph : AxPh
-- END AXIOM


-- AXIOM 2: "All inertial observers coordinatize the same set of events."
def AxEv : Prop := ∀ (m k : B), IOb m ∧ IOb k → ∀ (x : Point4), ∃ (y : Point4), events m x = events k y

axiom axev : AxEv
-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
def AxSf : Prop := ∀ (m : B), IOb m → ∀ (x : Point4), W m m x ↔ x.x = 0 ∧ x.y = 0 ∧ x.z = 0

axiom axsf : AxSf
-- END AXIOM

-- AXIOM 4a : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

def AxSm : Prop := ∀ (m k : B), IOb m ∧ IOb k → ∀ (x y x' y' : Point4), (x.t = y.t) ∧ (x'.t = y'.t) ∧ (events m x = events k x') ∧ (events m y = events k y) → spaceDistance x y = spaceDistance x' y'

axiom axsm : AxSm
-- END AXIOM


theorem notLightSpeed : ∀ (m k : B), ∀ (x y : Point4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k → ¬ spaceDistance x y = abs (x.t - y.t) := by
  intro m k x y ⟨mkx, mky, xney, iom, iok⟩ lightSpeed
  have  ⟨p1, ⟨p1ph, mp1x, mp1y⟩⟩ : ∃ p, Ph p ∧ W m p x ∧ W m p y := (axph m x y iom).mpr lightSpeed





















#exit
-- AXIOM 4b : "the speed of light is 1 for all inertial observers."
--def AxSmB : Prop := ∀ (m : B), IOb m → ∃ (p : B), Ph p ∧ W m p origin4 ∧ W m p xLightYear4

--axiom axsmb : AxSmB
-- END AXIOM

def myInequalityImplication : ∀ (a b : ℝ), ¬ a < b ∧ ¬ a = b → b < a := by
  intro a b h1
  rcases h1 with ⟨h1, h2⟩
  have h3 : a ≤ b ∨ b < a := le_or_lt _ _
  cases h3 with
    | inr h3 => assumption
    | inl h3 => have h4 : (a < b ∨ a = b) := (Iff.mp le_iff_lt_or_eq) h3
                cases h4 with
                  | inr h5 => exfalso; apply h2 h5
                  | inl h5 => exfalso; apply h1 h5


def noFasterThanLight : ∀ (m k : B), ∀ (x y : Point4), x ∈ wl m k ∧ y ∈ wl m k ∧ x ≠ y ∧ IOb m ∧ IOb k → spaceDistance y x < abs (y.t - x.t) := by
  intros m k x y h1

  rcases h1 with ⟨h1, h2, h3, h4, h5⟩
  apply myInequalityImplication
  constructor
  sorry
  sorry
