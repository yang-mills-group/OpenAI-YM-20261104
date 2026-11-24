import YM.PhysMS.Frame.Step

/-!
# Uniform polynomial cost between two ultraviolet measuring frames

On a fixed finite horizon the older physical labels, expressed in the basis at
any higher energy, cost at most a power of the ratio. Both the ultraviolet
threshold and the constants work simultaneously for every field vector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MeasuringFrameTransitionBound
open Set Filter Spec Climb Trace.Pilot PhysMS
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}

private theorem inverse_dilatation (d : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Icc (1:ℝ) 2, ∀ v : (Bel C.book).Field d,
      ‖Pert.Scale.gear C.labels d a v‖ ≤ M * ‖v‖ := by
  let B := Extra.FD.recorded C.labels d
  let c i := (2:ℝ)^(B.w i).1 * ‖B.b i‖ * ‖(B.b.coord i).toContinuousLinearMap‖
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => by unfold c; positivity), ?_⟩
  intro a ha v
  rw [Finset.sum_mul]
  nth_rw 1 [← B.b.sum_repr v]
  rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
  have h₀ : 0 ≤ a := zero_le_one.trans ha.1
  rw [map_smul, Pert.Scale.rare, norm_smul, norm_smul, Complex.norm_pow,
    Complex.norm_real, Real.norm_of_nonneg h₀]
  change ‖B.b.coord i v‖ * (a^(B.w i).1 * ‖B.b i‖) ≤ c i * ‖v‖
  refine (mul_le_mul ((B.b.coord i).toContinuousLinearMap.le_opNorm v)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₀ ha.2 _) (norm_nonneg _))
    (by positivity) (by positivity)).trans_eq ?_
  unfold c
  ring

private theorem half_step (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ r in trail, ∀ t ∈ Icc (1/2:ℝ) 1, ∀ x : S.Field d,
      ‖(J (t*r) d).symm x‖ ≤ B * ‖(J r d).symm x‖ := by
  obtain ⟨A, hA, h⟩ := Frame.comparison F d J H
  obtain ⟨M, _, hM⟩ := inverse_dilatation (C:=C) d
  refine ⟨max 1 (A*M), le_max_left .., ?_⟩
  filter_upwards [h (1/2) (by norm_num)] with r hr t ht x
  have hp : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ht.1
  have hi : t⁻¹ ∈ Icc (1:ℝ) 2 :=
    ⟨(one_le_inv₀ hp).mpr ht.2, (inv_le_comm₀ hp (by norm_num)).mpr (by simpa using ht.1)⟩
  let b := Frame.cocycle d J r t hp
  let u := (J (t*r) d).symm x
  let v := (J r d).symm x
  have hscale : Pert.Scale.gear C.labels d t (b u) = v := by
    apply (J r d).injective
    rw [show J r d _ = J (t*r) d u from Frame.cocycle_value d J u t r hp]
    simp [u, v]
  have hchange : b u = Pert.Scale.gear C.labels d t⁻¹ v := by
    rw [← hscale, Pert.Scale.gear_inverse C.labels hp.ne']
  change ‖u‖ ≤ _ * ‖v‖
  calc
    ‖u‖ = ‖b.symm (Pert.Scale.gear C.labels d t⁻¹ v)‖ := by rw [← hchange, b.symm_apply_apply]
    _ ≤ A * ‖Pert.Scale.gear C.labels d t⁻¹ v‖ := (hr t ht).2 _
    _ ≤ A * (M * ‖v‖) := mul_le_mul_of_nonneg_left (hM _ hi v) (zero_le_one.trans hA)
    _ ≤ max 1 (A*M) * ‖v‖ := by rw [← mul_assoc]; gcongr; exact le_max_right ..

/-- At the deeper scale `r/E`, the inverse measurement of any old label
costs at most `B*E^k`, uniformly in energy, ultraviolet length and vector. -/
theorem bound (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J) :
    ∃ (B : ℝ) (k : ℕ), 1 ≤ B ∧ ∀ᶠ r in trail, ∀ E : ℝ, 1 ≤ E →
      ∀ v : (Bel C.book).Field d, ‖(J (r/E) d).symm (J r d v)‖ ≤ B * E^k * ‖v‖ := by
  obtain ⟨B, hB, hstep⟩ := half_step F d J H
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (one_lt_two : (1:ℝ) < 2)
  obtain ⟨s, hs, hρ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hstep
  have hsmall : ∀ᶠ r in trail, r ∈ Ioc 0 s :=
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s, hs, subset_refl _⟩
  refine ⟨B, k, hB, ?_⟩
  filter_upwards [hsmall] with r hr E hE v
  let p (a : ℝ) := ‖(J (r/a) d).symm (J r d v)‖
  have go (n : ℕ) (a : ℝ) (ha : 1 ≤ a) (hn : a ≤ 2^n) :
      p a ≤ B * a^k * ‖v‖ := by
    induction n generalizing a with
    | zero =>
      have he : a = 1 := le_antisymm (by simpa using hn) ha
      simpa [p, he] using le_mul_of_one_le_left (norm_nonneg v) hB
    | succ n ih =>
      by_cases htwo : a ≤ 2
      · have hp : 0 < a := zero_lt_one.trans_le ha
        have hratio : a⁻¹ ∈ Icc (1/2:ℝ) 1 :=
          ⟨(le_inv_comm₀ (by norm_num) hp).mpr (by simpa using htwo), (inv_le_one₀ hp).mpr ha⟩
        have h := hρ hr a⁻¹ hratio (J r d v)
        refine (show p a ≤ B * ‖v‖ by simpa [p, div_eq_inv_mul] using h).trans ?_
        gcongr
        exact le_mul_of_one_le_right (zero_le_one.trans hB) (one_le_pow₀ ha)
      · have hb : 1 ≤ a/2 := by linarith only [htwo]
        have hp : 0 < a/2 := zero_lt_one.trans_le hb
        have hinner : r/(a/2) ∈ Ioc 0 s :=
          ⟨div_pos hr.1 hp, (div_le_self hr.1.le hb).trans hr.2⟩
        have hhalf := hρ hinner (1/2) ⟨le_rfl, by norm_num⟩ (J r d v)
        have hpos : 0 < a := zero_lt_one.trans_le ha
        have heq : (1/2) * (r/(a/2)) = r/a := by field_simp
        have hprev := ih (a/2) hb (by rw [pow_succ] at hn; linarith only [hn])
        calc
          p a ≤ B * p (a/2) := by simpa only [p, heq] using hhalf
          _ ≤ B * (B * (a/2)^k * ‖v‖) := mul_le_mul_of_nonneg_left hprev (zero_le_one.trans hB)
          _ ≤ B * (2^k * (a/2)^k * ‖v‖) := by gcongr
          _ = B * a^k * ‖v‖ := by rw [← mul_pow, show 2 * (a/2) = a by ring, mul_assoc]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt E (one_lt_two : (1:ℝ) < 2)
  exact go n E hE hn.le

end YM.Integration.MeasuringFrameTransitionBound
