/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2159ce4f-c6ae-40f7-8cc3-1bb342f34784

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧
  IOb B IB W m ∧ IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y
-/

import Relativity.lemmas
import Relativity.definitions


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

theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧
  IOb B IB W m ∧ IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y := by

  intro specRel m k x y ⟨mkx, mky, xney, iom, iok⟩ lightSpeed
  --SpecRel := axph B IB Ph W ∧ axev B IB W ∧ axsf B IB W ∧ axsm B IB W
  have axph := specRel.left
  have axev := specRel.right.left
  have axsf := specRel.right.right.left
  have axsm := specRel.right.right.right

  have  ⟨p, ⟨pph, mpx, mpy⟩⟩ : ∃ p, Ph p ∧ W m p x ∧ W m p y := (axph m x y iom).mpr lightSpeed
  have pEVmx : p ∈ events B W m x := by
    rw [events]
    exact mpx
  have pEVmy : p ∈ events B W m y := by
    rw [events]
    exact mpy
  have ⟨x', EVmxeqkx'⟩ := axev m k iom iok x
  have ⟨y', EVmyeqky'⟩ := axev m k iom iok y

  have EVneq1 : events B W m x ≠ events B W m y := x_ne_y_evx_ne_evy B IB Ph W axph x y m iom xney

  have EVneq2 : events B W k x' ≠ events B W k y' := by
    rw [← EVmxeqkx']
    rw [← EVmyeqky']
    exact EVneq1
  have x'neqy' : x' ≠ y' := by
    by_contra x'eqy'
    rw [x'eqy'] at EVneq2
    contradiction

  let x's : R3 := spatial x'
  let y's : R3 := spatial y'

  have x'sZero : x's = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] := by
    have  : W k k x' := by
      rw [← eventsToWorldview B W]
      rw [← EVmxeqkx']
      rw [eventsToWorldview B W]
      exact mkx
    have := axsf k iok x' this
    -- Since $x' 0 = 0$, $x' 1 = 0$, and $x' 2 = 0$, we have $x's = (0, 0, 0)$.
    ext i; fin_cases i <;> simp [x's, this];
    · exact this.1;
    · exact this.2.1;
    · -- By definition of spatial, we have spatial x' 2 = x' 2.
      simp [spatial, this]

  /-
  have x'sZero : x's = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] := by
    have  : W k k x' := by
      rw [← eventsToWorldview B W]
      rw [← EVmxeqkx']
      rw [eventsToWorldview B W]
      exact mkx
    have := axsf k iok x' this
    simp [x's]
    unfold spatial
    simp
    simp [this]
    aesop
-/
  have y'sZero : y's = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] := by
    apply Classical.byContradiction
    intro hy's_nonzero;
    have := axsf k iok y' ; simp_all +decide [ events ] ;
    simp_all +decide [ Set.ext_iff ];
    exact hy's_nonzero ( by ext i; fin_cases i <;> tauto )

  have spacedistSqx'y'0 : spaceDistanceSq x' y' = 0 := by
    unfold spaceDistanceSq
    change spaceNormSq (x's - y's) = 0
    rw [x'sZero, y'sZero]
    simp
    unfold spaceNormSq
    simp

  have x'teqy't : x' 3 = y' 3 := by
    have pEVkx' : p ∈ events B W k x' := by
      rw [← EVmxeqkx']
      exact pEVmx
    have pEVky' : p ∈ events B W k y' := by
      rw [← EVmyeqky']
      exact pEVmy
    have pWkx' : W k p x' := (eventsToWorldview B W p k x').mp pEVkx'
    have pWky' : W k p y' := (eventsToWorldview B W p k y').mp pEVky'
    have photon_k : ∃ p₀, Ph p₀ ∧ W k p₀ x' ∧ W k p₀ y' := ⟨p, pph, pWkx', pWky'⟩
    have lightspeed_k : spaceDistanceSq x' y' = timeDistanceSq x' y' :=
      (axph k x' y' iok).mp photon_k
    have  : 0 = (x' 3 - y' 3) ^ 2 := by
      have := Eq.trans spacedistSqx'y'0.symm lightspeed_k
      unfold timeDistanceSq at this
      exact this
    have  : (x' 3 - y' 3) ^ 2 = 0 := this.symm
    have  : (x' 3 - y' 3) = 0 := by
      have : (x' 3 - y' 3) * (x' 3 - y' 3) = 0 := by
        simpa [pow_two] using this
      exact mul_self_eq_zero.mp this
    exact sub_eq_zero.mp this

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