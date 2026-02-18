/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f04eaa0c-dad9-4a30-bab0-ed588c09bd9d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem notFasterThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y > timeDistanceSq x y
-/

import Harmonic.lemmas


set_option relaxedAutoImplicit true

-- Harmonic `generalize_proofs` tactic

variable (B : Type)

-- Bodies
variable (IB : B → Prop)

-- Inertial bodies predicate
variable (Ph : B → Prop)

-- Photon predicate
variable (W : B → B → R4 → Prop)

-- Worldview predicate

theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y := by
    contrapose!;
    rintro ⟨ m, k, x, y, h, h' ⟩;
    intro h''; have := h''.right.right.right; simp_all +decide [ SpecRel, axsm ] ;
    contrapose! this;
    use m, m;
    refine' ⟨ h.2.2.2.1, h.2.2.2.1, _ ⟩;
    use 0, EuclideanSpace.single 0 1, 0, 0 ; norm_num [ events ];
    unfold spaceDistanceSq; norm_num;
    unfold spaceNormSq; norm_num [ spatial ] ;
    norm_num [ Fin.ext_iff ]

theorem notFasterThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y > timeDistanceSq x y := by
    -- Otherwise, some inertial observer sees a body moving faster than light.
    intro h_specRel m k x y h_event
    by_contra h_contra
    have h_observer : ∃ m : B, IOb B IB W m ∧ (spaceDistanceSq x y > timeDistanceSq x y) := by
      exact ⟨ m, h_event.2.2.2.1, h_contra ⟩;
    have := h_specRel.2.2.2;
    have := this m m; simp_all +decide [ Set.ext_iff ] ;
    contrapose! this;
    use 0, 0, 0, EuclideanSpace.single 0 1; simp_all +decide [ events ] ;
    unfold spaceDistanceSq; norm_num;
    unfold spaceNormSq; norm_num [ spatial ] ;
    norm_num [ Fin.ext_iff ]