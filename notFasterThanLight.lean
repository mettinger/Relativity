import Relativity.lemmas
import Relativity.lemmas2
import Relativity.definitions
noncomputable section

open scoped RealInnerProductSpace
open EuclideanSpace
set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

theorem notFasterThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ IOb B IB W m ∧ IOb B IB W k →
  ¬ spaceDistanceSq x y > timeDistanceSq x y := by
    intro specRel m k x y ⟨hwmkx, hwmky, iom, iok⟩ spaceDistGreater
    --SpecRel := axph B IB Ph W ∧ axev B IB W ∧ axsf B IB W ∧ axsm B IB W
    have axph := specRel.left
    have axev := specRel.right.left
    have axsf := specRel.right.right.left
    have axsm := specRel.right.right.right
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, hwNotExist⟩⟩  := zwExist
    --obtain ⟨z, ⟨hxzLightlike, ⟨hnColxyz, hwNotExist⟩⟩⟩  := zwExist
    obtain ⟨x', hx'⟩ := axev m k iom iok x
    obtain ⟨y', hy'⟩ := axev m k iom iok y
    obtain ⟨z', hz'⟩ := axev m k iom iok z

    let x's : R3 := spatial x'
    let y's : R3 := spatial y'

    have x'sZero : x's = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] := by
      have  : W k k x' := by
        rw [← eventsToWorldview B W]
        rw [← hx']
        rw [eventsToWorldview B W]
        exact hwmkx
      have := axsf k iok x' this
      ext i; fin_cases i <;> simp [x's, this];
      · exact this.1;
      · exact this.2.1;
      · -- By definition of spatial, we have spatial x' 2 = x' 2.
        simp [spatial, this]

    have y'sZero : y's = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] := by
      apply Classical.byContradiction
      intro hy's_nonzero;
      have := axsf k iok y' ; simp_all +decide [ events ] ;
      simp_all +decide [ Set.ext_iff ];
      exact hy's_nonzero ( by ext i; fin_cases i <;> tauto )

    have hx'z'Lightlike : lightLike x' z' := lightLikeImplightLike B IB Ph W axph x z x' z' m k iom iok hxzLightlike hx' hz'

    have ⟨w', ⟨hllw'x', hllw'y', hllw'z'⟩⟩ : ∃ (w' : R4),
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := wExist x' y' z' x'sZero y'sZero hx'z'Lightlike
    obtain ⟨w, hwEvents⟩  := axev k m iok iom w'
    have hw : lightLike w x ∧ lightLike w y ∧ lightLike w z := by
      constructor
      case left := lightLikeImplightLike B IB Ph W axph w' x' w x k m iok iom hllw'x' hwEvents hx'.symm
      case right := by
        constructor
        case left := lightLikeImplightLike B IB Ph W axph w' y' w y k m iok iom hllw'y' hwEvents hy'.symm
        case right := lightLikeImplightLike B IB Ph W axph w' z' w z k m iok iom hllw'z' hwEvents hz'.symm
    have hwNot := hwNotExist w
    contradiction
