/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2eb29815-7452-4eb3-9bae-bdc0039c1bb7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb B IB W m ∧ IOb B IB W k →
  ¬ spaceDistanceSq x y = timeDistanceSq x y
-/

--Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib


--import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section

abbrev R3 := EuclideanSpace ℝ (Fin 3)

abbrev R4 := EuclideanSpace ℝ (Fin 4)

variable (B : Type)

-- Bodies
variable (IB : B → Prop)

-- Inertial bodies predicate
variable (Ph : B → Prop)

-- Photon predicate
variable (W : B → B → R4 → Prop)

-- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : R4 ) , W m b pt

-- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob B W m

-- Inertial observer predicate
def events (m : B) (x : R4) : Set B := { b | W m b x }

-- events observed by m at x
def wl (m b : B) : Set R4 := {x | W m b x}

-- worldline of b as viewed by m

def spatial (p : R4) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun x => p (Fin.castSucc x))

-- compute the squared norm of a 3d point
def spaceNormSq (p : R3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : R4) : ℝ := spaceNormSq ((spatial p) - (spatial q))

def timeDistanceSq (p q : R4) : ℝ := (p 3 - q 3) ^ 2

def lightLike (p q : R4) := spaceDistanceSq p q = timeDistanceSq p q

-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to
--           send out a light signal in any direction."
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

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events
--             if these two events are simultaneous for both of them."
abbrev axsm := ∀ (m k : B), IOb B IB W m ∧ IOb B IB W k →
                ∀ (x y x' y' : R4), (x 3 = y 3) ∧
                                    (x' 3 = y' 3) ∧
                                    (events B W m x = events B W k x') ∧
                                    (events B W m y = events B W k y') →
                                    spaceDistanceSq x y = spaceDistanceSq x' y'

-- END AXIOM

abbrev SpecRel := axph B IB Ph W ∧ axev B IB W ∧ axsf B IB W ∧ axsm B IB W

---------------------------------------------------------------

noncomputable section AristotleLemmas

/-
If two points in R4 have the same set of light-like separated points, they are equal.
-/
theorem light_cone_determined (x y : R4) : (∀ z, lightLike z x ↔ lightLike z y) → x = y := by
  intro h
  by_contra hxy;
  -- Let $a = x - y$. Then $Q(u) = 0 \implies Q(u + a) = 0$.
  set a : R4 := x - y
  have hQ : ∀ u : R4, (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = u 3 ^ 2) → ((u + a) 0 ^ 2 + (u + a) 1 ^ 2 + (u + a) 2 ^ 2 = (u + a) 3 ^ 2) := by
    simp +zetaDelta at *;
    intro u hu; specialize h ( u + x ) ; simp_all +decide [ lightLike ] ;
    unfold spaceDistanceSq timeDistanceSq at h; simp_all +decide [ add_sub_assoc ] ;
    unfold spaceNormSq spatial at h; simp_all +decide [ add_sub_assoc ] ;
  -- So for all null $u$, $2 B(u, a) + Q(a) = 0$.
  have hB : ∀ u : R4, (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = u 3 ^ 2) → (2 * (u 0 * a 0 + u 1 * a 1 + u 2 * a 2 - u 3 * a 3) + (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 - a 3 ^ 2) = 0) := by
    intro u hu; have := hQ u hu; norm_num at *; linarith;
  -- Taking $u=0$ gives $Q(a) = 0$.
  have hQa : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 - a 3 ^ 2 = 0 := by
    simpa using hB 0 ( by norm_num );
  -- Then $2 B(u, a) = 0$ for all null $u$.
  have hBa : ∀ u : R4, (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = u 3 ^ 2) → (u 0 * a 0 + u 1 * a 1 + u 2 * a 2 - u 3 * a 3 = 0) := by
    exact fun u hu => by linarith [ hB u hu ] ;
  -- Since the null cone spans the space, $a$ is orthogonal to everything, so $a=0$.
  have ha_zero : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 := by
    have := hBa ( fun i => if i.val = 0 then 1 else if i.val = 1 then 0 else if i.val = 2 then 0 else 1 ) ; ( have := hBa ( fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val = 2 then 0 else 1 ) ; ( have := hBa ( fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 1 else 1 ) ; ( norm_num at * ; ) ) );
    norm_num [ show a 0 = a 3 by linarith, show a 1 = a 3 by linarith, show a 2 = a 3 by linarith ] at * ; aesop;
  exact hxy <| sub_eq_zero.mp <| by ext i; fin_cases i <;> tauto;

/-
If two events are observed to contain the same set of bodies by an inertial observer, then the coordinates of the events are the same.
-/
theorem events_injective (m : B) (x y : R4) : SpecRel B IB Ph W → IOb B IB W m → events B W m x = events B W m y → x = y := by
  intro h h';
  intro h''; have := light_cone_determined x y; simp_all +decide [ Set.ext_iff ] ;
  apply this; intro z; exact (by
  constructor <;> intro hz <;> have := h.1 m z x h' <;> have := h.1 m z y h' <;> simp_all +decide [ events ];
  · exact this.mpr hz;
  · exact this.mp hz);

end AristotleLemmas

theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb B IB W m ∧ IOb B IB W k →
  ¬ spaceDistanceSq x y = timeDistanceSq x y := by
    simp +zetaDelta at *;
    intros h1 h2 h3 h4 m k x y hx hy hxy hm hk hlightlike
    obtain ⟨x', hx'⟩ := h2 m k hm hk x
    obtain ⟨y', hy'⟩ := h2 m k hm hk y
    have hx'_eq : W k k x' := by
      exact hx'.subset hx
    have hy'_eq : W k k y' := by
      exact hy'.subset hy
    have hx'_zero : x' 0 = 0 ∧ x' 1 = 0 ∧ x' 2 = 0 := by
      exact h3 k hk x' hx'_eq
    have hy'_zero : y' 0 = 0 ∧ y' 1 = 0 ∧ y' 2 = 0 := by
      exact h3 k hk y' hy'_eq
    have hx'_eq_y' : x' = y' := by
      have hx'_eq_y' : spaceDistanceSq x' y' = timeDistanceSq x' y' := by
        have := h1 m x y hm; simp_all +decide [ events ] ;
        have := h1 k x' y' hk; simp_all +decide [ Set.ext_iff ] ;
        have := h1 m x y hm; simp_all +decide [ axph ] ;
      simp +decide [ *, spaceDistanceSq, timeDistanceSq ] at hx'_eq_y';
      simp +decide [ *, spatial, spaceNormSq ] at hx'_eq_y';
      exact funext fun i => by fin_cases i <;> nlinarith!;
    have h_event_eq : (W m · x) = (W m · y) := by
      simp_all +decide [ Set.ext_iff, events ]
    have h_contradiction : x = y := by
      apply events_injective;
      exact ⟨ h1, h2, h3, h4 ⟩;
      exacts [ hm, by ext; simpa using congr_fun h_event_eq _ ]
    contradiction