import YM.RG.History
import YM.MatchingR2.SectionLaw
import YM.Push.SECTOR_MEASURE.Gauges

/-!
# Full conditional law at a Wilson step with Wilson input action

Link Haar, probability normalized at both levels, true tags including shared choices. Do not use
at general steps with inherited interactions without accounting for them. At the step considered
our input really is (as will be proved with the calibrated Family) the cutoff Wilson law; output
density includes every forced sector etc. No equality substituted for bounds on a representation.
Most of the lemma uses are charged at fixed period and cutoff in this file (bounded envelopes,
no proposed uniform pointwise lower bound for `coarseWeight`).
-/

set_option autoImplicit false
noncomputable section

namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff ENNReal Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}
variable (S : StepData c f) (β : ℝ)
set_option quotPrecheck false
local notation "Fine" => Config G f
local notation "Coarse" => Config G c

/-- Encoding only. -/
abbrev Key := Fin (Fintype.card S.Choices)
def tag : S.Choices ≃ Key S := Fintype.equivFin _
def fineWeight (β : ℝ) (U : Config G f) := bare β U / partition G f β
def tagged (j : S.Choices) (U : Fine) (V : Coarse) := S.likelihood U j * S.noise β (S.prediction U j) V
def ticket (j : S.Choices) (U : Fine) (V : Coarse) := fineWeight β U * tagged S β j U V
def coarseWeight (V : Coarse) := S.push β (fineWeight β : Fine → ℝ) V

section bills
variable {X : Type*} [MeasurableSpace X]

theorem envelope_cart {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [CompactSpace Y] (f : Y → ℝ) (hf : Continuous f) : Envelope f := by
  obtain ⟨M,hM⟩ := (isCompact_range hf.norm).bddAbove
  exact ⟨hf.measurable,M,fun y => hM ⟨y,rfl⟩⟩
theorem envelope_readTag {κ : Type*} [MeasurableSpace κ] [Fintype κ] [MeasurableSingletonClass κ]
    {g : X → κ} {f : κ → X → ℝ} (hg : Measurable g) (h : ∀ i, Envelope (f i)) :
    Envelope fun x => f (g x) x := by
  classical
  have ht (i : κ) : Envelope fun x => if g x = i then f i x else 0 :=
    Envelope.piece (show MeasurableSet {x : X | g x = i} from hg (measurableSet_singleton i))
      (h i) (Envelope.const (V := X) 0)
  have H (x) : ∑ i : κ, (if g x = i then f i x else 0) = f (g x) x := by simp
  simpa only [H] using (Envelope.sum Finset.univ _ ht)
lemma fine_weight_pos (U : Fine) : 0 < fineWeight β U := div_pos (bare_pos _ _) (partition_pos _)
lemma fine_weight_env : Envelope (fineWeight (G:=G) (f:=f) β) :=
  envelope_cart _ ((bare_cont β).div_const _)
lemma noise_pos (Q V : Coarse) : 0 < S.noise β Q V :=
  Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos _)) (Real.exp_pos _)
lemma tagged_ge (j : S.Choices) (U : Fine) (V : Coarse) : 0 ≤ tagged S β j U V :=
  mul_nonneg (S.likelihood_pos U j) (noise_pos S β ..).le
lemma ticket_nn (j : S.Choices) (U : Fine) (V : Coarse) : 0 ≤ ticket S β j U V :=
  mul_nonneg (fine_weight_pos β U).le (tagged_ge S β ..)
variable (H : S.patch.Branches S.kernel G)
include H
lemma tagged_env {U : X → Fine} (hu : Measurable U) {V : X → Coarse} (hv : Measurable V) (j : S.Choices) :
    Envelope fun x => tagged S β j (U x) (V x) := by
  obtain ⟨C,hC⟩ := S.density_bound H β
  refine ⟨?_,C,fun i => ?_⟩
  · unfold tagged
    have hQ : Measurable (fun x => (S.prediction (U x) j, V x)) :=
      ((S.prediction_meas H j).comp hu).prodMk hv
    have hm : Measurable (fun x => S.noise β (S.prediction (U x) j) (V x)) :=
      show Measurable ((fun p:Coarse×Coarse=>S.noise β p.1 p.2) ∘ fun x => (S.prediction (U x) j, V x)) from
      Measurable.comp (S.noise_cont (G:=G) β).measurable hQ
    exact ((S.likelihood_meas H j).comp hu).mul hm
  calc
    _ = tagged S β j (U i) (V i) := Real.norm_of_nonneg (tagged_ge S β j (U i) (V i))
    _ ≤ ∑ k:S.Choices, tagged S β k (U i) (V i) :=
      Finset.single_le_sum (f:=fun j => tagged S β j (U i) (V i)) (fun k _ => tagged_ge S β k (U i) (V i)) (Finset.mem_univ j)
    _ ≤ C := hC (U i) (V i)
lemma ticket_env {U : X → Fine} (hu : Measurable U) {V : X → Coarse} (hv : Measurable V) (j : S.Choices) :
    Envelope fun x => ticket S β j (U x) (V x) :=
  ((envelope_comp (fine_weight_env β) hu).mul (tagged_env S β H hu hv j))

lemma coarse_income (V : Coarse) :
    coarseWeight S β V = ∑ j : S.Choices, ∫ U : Fine, ticket S β j U V ∂prior G f := by
  unfold coarseWeight StepData.push StepData.density
  simp_rw [smul_eq_mul, Finset.sum_mul]
  rw [← integral_finsetSum (μ:=prior G f) Finset.univ (f:=fun i U=>ticket S β i U V) (fun i _ => (ticket_env S β H (U:=id) measurable_id (V:=fun _=>V) measurable_const i).integrable _)]
  congr 1; ext1 U; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..
lemma density_bright (U : Fine) (V : Coarse) : 0 < S.density β U V := by
  refine Finset.sum_pos' (fun i _ => tagged_ge S β i U V) ?_
  obtain ⟨i,hi⟩ : ∃ i, 0 < S.likelihood U i := by
    by_contra! h; have hz : ∑ i, S.likelihood U i = 0 := Finset.sum_eq_zero
      fun i _ => le_antisymm (h i) (S.likelihood_pos ..)
    rw [S.chosen H] at hz; exact one_ne_zero hz
  exact ⟨i,Finset.mem_univ _,mul_pos hi (noise_pos S β _ _)⟩
lemma coarse_weight_pos (V : Coarse) : 0 < coarseWeight S β V := by
  have hf (U : Fine) : 0 < S.density β U V • fineWeight β U := mul_pos (density_bright S β H U V) (fine_weight_pos β U)
  change 0 < ∫ U, (S.density β U V • fineWeight β U) ∂_
  have hU := (fine_weight_env β).integrable (prior G f)
  apply (integral_pos_iff_support_of_nonneg (fun i => (hf i).le) (S.push_slice (S.isKernel H β) V _ hU)).2
  rw [Set.eq_univ_of_forall (s:= (fun U => S.density β U V • fineWeight β U).support) (fun U => (hf U).ne'), measure_univ]; simp
lemma coarse_total : ∫ V : Coarse, coarseWeight S β V ∂prior G c = 1 := by
  change ∫ V, S.push β _ V ∂_ = _
  rw [StepData.push_integral (S.isKernel H β) _ ((fine_weight_env β).integrable (prior G f))]
  unfold fineWeight; rw [integral_div,← partition,div_self (partition_pos _).ne']
end bills
end YM.MatchingR2.Top
