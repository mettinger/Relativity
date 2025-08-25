import Mathlib
open scoped RealInnerProductSpace
noncomputable section


abbrev R4 := EuclideanSpace ℝ (Fin 4)
abbrev R3 := EuclideanSpace ℝ (Fin 3)


def spatial (p : R4) : R3 :=
  fun x : Fin 3 =>
    match x with
    | 0 => p 0
    | 1 => p 1
    | 2 => p 2

--def spaceNormSq (p : R3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
def spaceNormSq (p : R3) : ℝ := ‖p‖ ^ 2

def spaceDistanceSq (p q : R4) : ℝ := spaceNormSq  (spatial p - spatial q)

axiom B : Type -- Bodies
axiom IB : B → Prop -- Inertial bodies predicate
axiom Ph : B → Prop -- Photon predicate
axiom W : B → B → R4 → Prop -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : R4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob m -- Inertial observer predicate
def events (m : B) (x : R4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set R4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to send out a light signal in any direction."

axiom axph : ∀ (m : B), ∀ (x y : R4), IOb m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = abs (x 3 - y 3) ^2))

-- END AXIOM

-- AXIOM 2: "All inertial observers coordinatize the same set of events."
axiom axev : ∀ (m k : B), IOb m → IOb k → ∀ (x : R4), ∃ (y : R4), events m x = events k y

-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
axiom axsf : ∀ (m : B), IOb m → ∀ (x : R4), W m m x → x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0

-- END AXIOM

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

axiom axsm : ∀ (m k : B), IOb m ∧ IOb k → ∀ (x y x' y' : R4), (x 3 = y 3) ∧ (x' 3 = y' 3) ∧ (events m x = events k x') ∧ (events m y = events k y) → spaceDistanceSq x y = spaceDistanceSq x' y'

-- END AXIOM

theorem zExistsxtneyt : ∀ (x y : R4), spaceDistanceSq x y > abs (y 3 - x 3) → x 3 ≠ y 3 →
            ∃ (z : R4), spaceDistanceSq z x = abs ( z 3 - x 3) ^ 2
            ∧ (z 3 - x 3) ≠ 0
            ∧ ⟪ spatial z - spatial x, spatial z - spatial y ⟫ = 0 := sorry

theorem zExistsxteqyt : ∀ (x y : R4), spaceDistanceSq x y > abs (y 3 - x 3) → x 3 = y 3 →
            ∃ (z : R4), spaceDistanceSq z x = abs ( z 3 - x 3) ^ 2
            ∧ (z 3 - x 3) ≠ 0
            ∧ ⟪ spatial z - spatial x, spatial y - spatial x ⟫ = 0 := sorry

theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨hwmkx, hwmky, xney, iob, iok⟩ spaceDistGreater
    sorry

end
