import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section

abbrev R4 := EuclideanSpace ℝ (Fin 4)
abbrev R3 := EuclideanSpace ℝ (Fin 3)

def spatial (p : R4) : R3 :=
  -- Convert the raw function into the EuclideanSpace type
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun x => p (Fin.castSucc x))

-- compute the norm of a 3d point
def spaceNormSq (p : R3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : R4) : ℝ := spaceNormSq ((spatial p) - (spatial q))
def timeDistanceSq (p q : R4) : ℝ := (p 3 - q 3) ^ 2

def lightLike (p q : R4) := spaceDistanceSq p q = timeDistanceSq p q


variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : R4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob B W m -- Inertial observer predicate
def events (m : B) (x : R4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set R4 := {x | W m b x} -- worldline of b as viewed by m

-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to send out a light signal in any direction."
abbrev axph := ∀ (m : B), ∀ (x y : R4), IOb B IB W m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = timeDistanceSq x y))

-- END AXIOM

-- AXIOM 2: "All inertial observers coordinatize the same set of events."
abbrev axev := ∀ (m k : B), IOb B IB W m → IOb B IB W k →
             ∀ (x : R4), ∃ (y : R4), events B W m x = events B W k y

-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
abbrev axsf := ∀ (m : B), IOb B IB W m → ∀ (x : R4), W m m x → x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0

-- END AXIOM

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events if these two events are simultaneous for both of them."

abbrev axsm := ∀ (m k : B), IOb B IB W m ∧ IOb B IB W k →
                ∀ (x y x' y' : R4), (x 3 = y 3) ∧
                                    (x' 3 = y' 3) ∧
                                    (events B W m x = events B W k x') ∧
                                    (events B W m y = events B W k y) →
                                    spaceDistanceSq x y = spaceDistanceSq x' y'

-- END AXIOM

abbrev SpecRel := axph B IB Ph W ∧ axev B IB W ∧ axsf B IB W ∧ axsm B IB W
