import Relativity.definitions
set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic


variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate


theorem norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

theorem norm_sq_is_sum_of_squares : ∀ (v : R3), (v 0)^2 + (v 1)^2 + (v 2)^2 = (norm v) ^ 2 := by
  intro v
  rw [EuclideanSpace.norm_sq_eq]
  norm_num
  have hcoords :
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = ∑ x : Fin 3, (v x) ^ 2 := by
    simpa using
      (Fin.sum_univ_three (fun x : Fin 3 => (v x) ^ 2)).symm
  exact hcoords

theorem spatialDiff : ∀ (x y : R4), spatial x - spatial y = ![x 0 - y 0, x 1 - y 1, x 2 - y 2] := by
  intros x y
  ext i
  simp only [spatial];
  fin_cases i <;> rfl


theorem eventsToWorldview : ∀ (b ob : B), ∀ (x : R4), b ∈ events B W ob x ↔ W ob b x := by
  simp [events]

theorem timeDistanceComm : ∀ (x y : R4), timeDistanceSq x y = timeDistanceSq y x := by
  intro x y
  unfold timeDistanceSq
  ring

theorem spaceDistanceComm : ∀ (x y: R4), spaceDistanceSq x y = spaceDistanceSq y x := by
  intro x y
  simp [spaceDistanceSq];
  simp [spaceNormSq]
  ring

theorem lightLikeSymm : ∀ (x y : R4), lightLike x y → lightLike y x := by
  intro x y hllxy
  unfold lightLike at *
  rw [← spaceDistanceComm x y]
  rw [← timeDistanceComm x y]
  assumption

theorem lightLikeImplightLike : axph B IB Ph W →
  (∀ (x y x' y' : R4), ∀ (m k : B), IOb B IB W m →
                                    IOb B IB W k →
                                    lightLike x y →
                                    events B W m x = events B W k x' ->
                                    events B W m y = events B W k y' →
                                    lightLike x' y') := by
  intro h_axph x y x' y' m k hm hk hxy hx hy
  obtain ⟨p, hp⟩ : ∃ p, Ph p ∧ W m p x ∧ W m p y := by
    exact h_axph m x y hm |>.2 hxy;
  have hp_events : W k p x' ∧ W k p y' := by
    exact ⟨ hx.subset hp.2.1, hy.subset hp.2.2 ⟩;
  exact h_axph k x' y' hk |>.1 ⟨ p, hp.1, hp_events.1, hp_events.2 ⟩


theorem sp_tm_eq_eq : ∀ (x y: R4), spaceDistanceSq x y = 0 → x 3 = y 3 → x = y := by
  intros x y h_space h_time
  have h_comp : x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
    have h_comp : (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 = 0 := by
      convert h_space using 1;
    exact ⟨ by nlinarith only [ h_comp ], by nlinarith only [ h_comp ], by nlinarith only [ h_comp ] ⟩;
  ext i; fin_cases i <;> tauto


theorem spanNeg {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) : Submodule.span ℝ {v} = Submodule.span ℝ {-v} := by
  rw [← Submodule.span_neg]
  simp

theorem affineSpanDef : ∀ (x y z : R4), y ∈ affineSpan ℝ ({x, z} : Set R4) → ∃ (k : ℝ), y = x + (k • (z- x)) := by
  intro x y z h;
  obtain ⟨ k₁, k₂, hk₁, hk₂, hk ⟩ := h;
  rw [ vectorSpan_pair ] at hk₂;
  rw [ Submodule.mem_span_singleton ] at hk₂;
  rcases hk₂ with ⟨ k, rfl ⟩ ; rcases k₂ with ( rfl | rfl ) <;> norm_num at *;
  · exact ⟨ -k, by rw [ hk ] ; ext ; norm_num ; ring ⟩;
  · exact ⟨ 1 - k, by rw [ hk ] ; ext ; norm_num ; ring ⟩


theorem lightLikeSpan : ∀ (x y z : R4), lightLike x z → y ∈ affineSpan ℝ ({x, z} : Set R4)
  → lightLike x y := by
  intro x y z;
  unfold lightLike;
  unfold spaceDistanceSq timeDistanceSq;
  intro h_lightlike h_affine
  obtain ⟨t, ht⟩ : ∃ t : ℝ, y = x + t • (z - x) := by
    have h_affine_def : y ∈ affineSpan ℝ ({x, z} : Set R4) → ∃ t : ℝ, y = x + t • (z - x) := by
      apply affineSpanDef;
    exact h_affine_def h_affine;
  simp only [ht, spatial] at *;
  simp [spaceNormSq] at *;
  linear_combination' h_lightlike * t ^ 2

noncomputable section AristotleLemmas

lemma lightLike_reflection (x y : R4) (h_time : y 3 > x 3) (h_light : lightLike x y) : ∃ z, lightLike x z ∧ ¬ lightLike y z := by
  -- Define z such that spatial z = 2 • spatial x - spatial y and z 3 = y 3.
  use (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![2 * x 0 - y 0, 2 * x 1 - y 1, 2 * x 2 - y 2, y 3];
  unfold lightLike at *;
  unfold spaceDistanceSq timeDistanceSq at *;
  unfold spaceNormSq spatial at *;
  simp +zetaDelta at *;
  exact ⟨ by linarith, by nlinarith ⟩

end AristotleLemmas

theorem oppDirection : axph B IB Ph W → ∀ (m : B) (x y : R4), IOb B IB W m →
    y 3 > x 3 →
    spaceDistanceSq x y = (x 3 - y 3) ^ 2 →
    ∃ (p : B), Ph p ∧ W m p x ∧ ¬ W m p y := by
    intro h m x y hm hxy hxy_eq
    obtain ⟨z, hz⟩ := (lightLike_reflection (x := x) (y := y) hxy (by
    exact hxy_eq));
    obtain ⟨ p, hp ⟩ := h m x z hm |>.2 hz.1;
    refine' ⟨ p, hp.1, hp.2.1, fun hy => hz.2 _ ⟩;
    exact h m y z hm |>.1 ⟨ p, hp.1, hy, hp.2.2 ⟩

theorem x_ne_y_evx_ne_evy : axph B IB Ph W → ∀ (x y : R4) (b : B), IOb B IB W b →
  x ≠ y →
  events B W b x ≠ events B W b y := by
  intro h x y b hb hxy h_event_eq
  have h_light : lightLike x y := by
    -- Since $x \neq y$, there must be a photon connecting them. By the Axiom of the Speed of Light, this implies $spaceDistanceSq x y = timeDistanceSq x y$.
    have h_photon : ∃ p : B, Ph p ∧ W b p x ∧ W b p y := by
      obtain ⟨p, hp⟩ : ∃ p : B, Ph p ∧ W b p x := by
        -- By the axiom axph, since b is an inertial observer, there exists a photon p such that W b p x.
        have h_photon : ∃ p : B, Ph p ∧ W b p x := by
          have := h b x x hb
          simp_all +decide [ spaceDistanceSq, timeDistanceSq ];
          unfold spaceNormSq; norm_num;
        exact h_photon;
      exact ⟨ p, hp.1, hp.2, h_event_eq.subset hp.2 ⟩;
    exact h b x y hb |>.1 h_photon;
  obtain ⟨q, hq⟩ : ∃ q : B, Ph q ∧ W b q x ∧ ¬W b q y := by
    by_cases hxy' : x 3 < y 3;
    · apply_rules [ oppDirection ];
    · by_cases hxy'' : y 3 < x 3;
      · have := oppDirection B IB Ph W h b y x hb hxy'' ?_ <;> simp_all +decide [ lightLike ];
        · exact False.elim <| this.elim fun q hq => hq.2.2 <| h_event_eq.symm.subset hq.2.1;
        · rw [ spaceDistanceComm, h_light ] ; ring;
          unfold timeDistanceSq; ring;
      · simp_all +decide [ lightLike ];
        unfold spaceDistanceSq timeDistanceSq at h_light;
        unfold spaceNormSq at h_light; simp_all +decide;
        exact False.elim <| hxy <| by ext i; fin_cases i <;> nlinarith! only [ h_light, hxy', hxy'' ] ;
  exact hq.2.2 ( h_event_eq.subset hq.2.1 )

theorem x_ne_y_imp_x'_ne_y' : axph B IB Ph W → ∀ (x y x' y': R4), x ≠ y →
  ∀ (m k : B), IOb B IB W m →
              IOb B IB W k →
              events B W m x = events B W k x' →
              events B W m y = events B W k y' →
              x' ≠ y' := by
              intros h_axph x y x' y' hxy m k hm hk h_events_m h_events_k
              have h_events_ne : events B W m x ≠ events B W m y := by
                -- By the definition of events, if x ≠ y, then the sets of bodies observed at x and y by m are different.
                have h_events_ne : ∀ (x y : R4), x ≠ y → events B W m x ≠ events B W m y := by
                  -- By the uniqueness of events in the coordinate system of an inertial observer, if x ≠ y, then events B W m x ≠ events B W m y.
                  intros x y hxy
                  apply x_ne_y_evx_ne_evy B IB Ph W h_axph x y m hm hxy;
                -- Apply the hypothesis `h_events_ne` with the given `hxy`.
                apply h_events_ne x y hxy;
              contrapose! h_events_ne; aesop;
