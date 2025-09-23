import Relativity.lemmas2
open scoped RealInnerProductSpace
open EuclideanSpace

#check dist_add_dist_eq_iff

theorem tangentPlaneToCone : ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y →
  ∃ (z : R4), x ≠ z ∧ lightLike x z ∧ ∀ (s t : R4), affineSpan ℝ ({s,t} : Set R4) ≤  affineSpan ℝ ({x, y, z} : Set R4) → lightLike s t → (affineSpan ℝ ({s,t} : Set R4)).Parallel  (affineSpan ℝ ({x,z} : Set R4)) := sorry

lemma lightLikeSpanEq : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z →
  (x 3 = w 3 ∨ z 3 = w 3) → w ∈ affineSpan ℝ {x, z} := sorry

lemma lightLikeSpanLt : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z →
  (x 3 < z 3 ∧ z 3 < w 3) ∨ (x 3 < w 3 ∧ w 3 < z 3) ∨ (w 3 < x 3 ∧ x 3 < z 3) →
  w ∈ affineSpan ℝ {x, z} := sorry

lemma lightLikeEq : ∀ (x y : R4), lightLike x y → x 3 = y 3 → x = y := sorry

theorem lightLikeSpan' : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z → x ≠ z →
  w ∈ affineSpan ℝ {x, z} := by
    intro x z w hllxz hllwx hllwz hxnez
    by_cases hxz : x 3 ≤ z 3
    by_cases hzw : z 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hxz
    apply le_iff_eq_or_lt.mp at hzw
    obtain h1|h2 := hxz
    have := lightLikeEq x z hllxz h1
    contradiction
    obtain h3|h4 := hzw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inr h3)
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inl (And.intro h2 h4))
    apply le_iff_eq_or_lt.mp at hxz
    obtain h1|h2 := hxz
    have := lightLikeEq x z hllxz h1
    contradiction
    apply not_le.mp at hzw
    by_cases hxw : x 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hxw
    obtain h1|h2 := hxw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inl h1)
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inr (Or.inl (And.intro h2 hzw)))
    apply not_le.mp at hxw
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inr (Or.inr (And.intro hxw h2)))
    apply not_le.mp at hxz
    by_cases hwx : w 3 ≤ x 3
    apply le_iff_eq_or_lt.mp at hwx
    obtain h1|h2 := hwx
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inl h1.symm)
    by_cases hzw : z 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hzw
    obtain h1|h3 := hzw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inr h1)
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inr (Or.inl (And.intro h3 h2)))
    simpa [Set.pair_comm] using this
    apply not_le.mp at hzw
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inr (Or.inr (And.intro hzw hxz)))
    simpa [Set.pair_comm] using this
    apply not_le.mp at hwx
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inl (And.intro hxz hwx))
    simpa [Set.pair_comm] using this

theorem zExist : ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y → ∃ (z : R4),
  lightLike x z ∧ ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := by
    intro x y hsdgttd
    have := tangentPlaneToCone x y hsdgttd
    obtain ⟨z, ⟨hxnez, hllxz, hparallel⟩⟩  := this
    use z
    constructor
    exact hllxz
    by_contra hw
    push_neg at hw
    obtain ⟨w,⟨hllwx, hllwy, hllwz⟩ ⟩ := hw
    have hwxyz := hparallel w y
    have hwInxzSpan: w ∈ affineSpan ℝ {x,z} := lightLikeSpan' x z w hllxz hllwx hllwz hxnez
    have haffineSub: affineSpan ℝ {w, y} ≤ affineSpan ℝ {x, y, z} := by
      have : {w,y}  ⊆ ((affineSpan ℝ {x, y, z}) : Set R4) := by
        simp only [Set.insert_subset_iff]
        constructor
        have hle :
            affineSpan ℝ ({x, z} : Set R4) ≤
              affineSpan ℝ ({x, y, z} : Set R4) := by
          apply affineSpan_mono
          intro t ht
          have hxz : t = x ∨ t = z := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
          rcases hxz with rfl | rfl
          · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
          · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hle hwInxzSpan
        have hy_mem : y ∈ (affineSpan ℝ {x, y, z}) := by
          have : y ∈ ({x,y,z} : Set R4) := by simp
          apply mem_affineSpan ℝ this
        simpa [Set.singleton_subset_iff] using hy_mem
      exact affineSpan_le.mpr this
    have hAffineParallel := hwxyz haffineSub hllwy
    apply AffineSubspace.Parallel.direction_eq at hAffineParallel
    have hn : ((affineSpan ℝ {w, y} : Set R4) ∩ (affineSpan ℝ {x, z} : Set R4)).Nonempty := by
      use w
      constructor
      have : w ∈ ({w,y} : Set R4) := by simp
      have := mem_spanPoints ℝ w {w,y} this
      assumption
      assumption
    have hAffinesEqual := AffineSubspace.ext_of_direction_eq hAffineParallel hn
    have : affineSpan ℝ {w, y} = affineSpan ℝ {x, z} → spanPoints ℝ {w,y} = spanPoints ℝ {x,z} := by
      intro h
      have h' := congrArg (fun S : AffineSubspace ℝ R4 => (S : Set R4)) h
      simpa [coe_affineSpan] using h'
    apply this at hAffinesEqual
    have hSetsEqual : (affineSpan ℝ {w, y} : Set R4) = (affineSpan ℝ {x,z} : Set R4) := by
      rw [coe_affineSpan]
      rw [coe_affineSpan]
      rw [hAffinesEqual]
    have : y ∈ ({w,y} : Set R4) := by simp
    have hyInwy := mem_spanPoints ℝ y {w,y} this
    have : y ∈ (affineSpan ℝ {x,z} : Set R4) := by
      rw[coe_affineSpan]
      rw [← hAffinesEqual]
      assumption
    have hynInxz : y ∉ spanPoints ℝ ({x,z}: Set R4) := by
      intro hyInSpanxz
      have hllxy := lightLikeSpan x y z hllxz hyInSpanxz
      unfold lightLike at hllxy
      rw [hllxy] at hsdgttd
      linarith
    contradiction

theorem wExist : ∀ (x y z : R4), spatial x = ![0,0,0] → spatial y = ![0,0,0]
  → lightLike x z → ∃ (w : R4), lightLike w x ∧ lightLike w y ∧ lightLike w z := by
    intro x y z xsZero ysZero lightLikexz

    let dir := affineSpan ℝ ({x, z} : Set R4)
    let w := EuclideanGeometry.orthogonalProjection dir (y - x)
    have hwInDir := EuclideanGeometry.orthogonalProjection_mem (s := dir) (p := y - x)
    use w
    constructor
    case h.left := (lightLikeSymm x w) (lightLikeSpan x w z lightLikexz hwInDir)
    constructor
    case h.right.right := by
      have : ({x, z} : Set R4) = ({z, x} : Set R4) := by apply Set.pair_comm
      have : affineSpan ℝ ({x, z} : Set R4) = affineSpan ℝ ({z, x} : Set R4) := by
        rw [← this]
      have : ↑w ∈ affineSpan ℝ {z, x} := by
        conv =>
          congr
          rw [← this]
          rfl
        apply hwInDir
      exact (lightLikeSymm z w) (lightLikeSpan z w x ((lightLikeSymm x z) lightLikexz) this)
    case h.right.left := by
      unfold lightLike
      sorry

theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > timeDistanceSq x y := by
    intro m k x y ⟨hwmkx, hwmky, iom, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, hwNotExist⟩⟩  := zwExist
    --obtain ⟨z, ⟨hxzLightlike, ⟨hnColxyz, hwNotExist⟩⟩⟩  := zwExist
    obtain ⟨x', hx'⟩ := axev m k iom iok x
    obtain ⟨y', hy'⟩ := axev m k iom iok y
    obtain ⟨z', hz'⟩ := axev m k iom iok z

    have x'sZero : spatial x' = ![0,0,0] := by
      have wkkx' : W k k x' := by
        apply (eventsToWorldview k k x').mp
        rw [← hx']
        apply (eventsToWorldview k m x).mpr
        assumption
      have hx's000 := axsf k iok x' wkkx'
      unfold spatial
      ext i
      aesop

    have y'sZero : spatial y' = ![0,0,0] := by
      have wkky' : W k k y' := by
        apply (eventsToWorldview k k y').mp
        rw [← hy']
        apply (eventsToWorldview k m y).mpr
        assumption
      have hy's000 := axsf k iok y' wkky'
      unfold spatial
      ext i
      aesop

    have hx'z'Lightlike : lightLike x' z' := lightLikeImplightLike x z x' z' m k iom iok hxzLightlike hx' hz'

    have ⟨w', ⟨hllw'x', hllw'y', hllw'z'⟩⟩ : ∃ (w' : R4),
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := wExist x' y' z' x'sZero y'sZero hx'z'Lightlike
    obtain ⟨w, hwEvents⟩  := axev k m iok iom w'
    have hw : lightLike w x ∧ lightLike w y ∧ lightLike w z := by
      constructor
      case left := lightLikeImplightLike w' x' w x k m iok iom hllw'x' hwEvents hx'.symm
      case right := by
        constructor
        case left := lightLikeImplightLike w' y' w y k m iok iom hllw'y' hwEvents hy'.symm
        case right := lightLikeImplightLike w' z' w z k m iok iom hllw'z' hwEvents hz'.symm
    have hwNot := hwNotExist w
    contradiction
