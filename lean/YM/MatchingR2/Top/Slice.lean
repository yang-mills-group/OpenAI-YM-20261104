import YM.MatchingR2.Top.Raw
import YM.Tree.Cut

/-! Gauge localization BEFORE any estimate. Retaining the original V in the conditional kernel
index; V read by the formal charts is `turned`. Future pricing will be centered at `o`.

Pack exactly against selected forest, not conditioning on a no-hole event or dropping nonzero K
in the step. Ignore fallback values of calculus definitions: Envelope hypotheses retained.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set Tree Push.SectorMeasure
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side}
variable (S : StepData c f) (F : Forest S.ratio) (β : ℝ)
set_option quotPrecheck false
local notation "Fine" => Config G f
local notation "Coarse" => Config G c

def pivot (o : Site c) (V : Coarse) (x : Site c) :=
  Axial.traveller (allAxes 1) (expandAt o V) 0 (lift (x - o))
def turned (o : Site c) (V : Coarse) : Coarse := Lattice.gauge (pivot o V) V
lemma pivot_continuous (o : Site c) : Continuous (pivot (G:=G) o) := by
  apply continuous_pi; intro x; unfold pivot Axial.traveller expandAt; fun_prop
lemma turned_continuous (o : Site c) : Continuous (turned (G:=G) o) := by
  have he := pivot_continuous (G:=G) o
  apply continuous_pi; intro e
  unfold turned Lattice.gauge
  exact (((continuous_apply e.1).comp he).mul (continuous_apply e)).mul (((continuous_apply (e.1+step e.2)).comp he).inv)

-- class of tests used in carrying positivity & bounds from the original kernel.
abbrev Covariant (fct : Fine → Coarse → ℝ) :=
    ∀ (t : Site f → G.El) (U : Fine) (V : Coarse),
      fct (Lattice.gauge t U) (Lattice.gauge (t ∘ S.ratio.embed) V) = fct U V

lemma noise_same (Q V : Coarse) (g : Site c → G.El) :
    S.noise β (Lattice.gauge g Q) (Lattice.gauge g V) = S.noise β Q V := by
  unfold StepData.noise StepData.penaltyWeight
  apply Finset.prod_congr rfl; intro e _; unfold Lattice.gauge
  rw [show g e.1 * V e * (g (e.1+step e.2))⁻¹ * (g e.1 * Q e * (g (e.1+step e.2))⁻¹)⁻¹ =
      g e.1 * (V e * (Q e)⁻¹) * (g e.1)⁻¹ by group, G.price_conj]
lemma ticket_same (H : S.patch.Branches S.kernel G) (i : S.Choices) : Covariant S (G:=G) (ticket S β i) := by
  intro t U V
  unfold ticket tagged fineWeight
  rw [bare_gauge,(choice_gauge H U i t).1, (choice_gauge H U i t).2,noise_same]

private lemma sums_cov (H : S.patch.Branches S.kernel G) (i : S.Choices) (V : Coarse)
    (o : Site c) (A : Fine → Coarse → ℝ)
    (ha : Envelope (uncurry A)) (hA : Covariant S A) :
    ∫ a, ticket S β i (F.drape a) (turned o V)*A (F.drape a) (turned o V) ∂F.order G =
    ∫ U : Fine, ticket S β i U V * A U V ∂prior G f := by
  let g U V := ticket S β i U V * A U V
  let W := turned o V
  have hi : Covariant S g := by intro t U W; unfold g; rw [ticket_same S β H i, hA t]
  have hs : Envelope (fun U => g U W) :=
    (ticket_env S β H (U:=id) measurable_id (V:=fun _=>W) measurable_const i).mul
      (envelope_comp ha (measurable_id.prodMk (measurable_const (a:=W))))
  have hm (k:Site c→G.El) : ((k ∘ S.ratio.parent) ∘ S.ratio.embed) = k := by
    funext x; dsimp; rw [S.ratio.embed_parent]
  let k := pivot o V; let q := k ∘ S.ratio.parent
  calc
    _ = ∫ U : Fine, g U W ∂prior G f := (F.pack _ (hs.integrable _) fun t ht U => by
      have h : Lattice.gauge (t ∘ S.ratio.embed) W = W := by funext e; simp [Lattice.gauge,ht]
      have he := hi t U W; rwa [h] at he).symm
    _ = ∫ U : Fine, g (Lattice.gauge q U) W ∂prior G f := by
       have hp := prior_gauge q
       have he := hs.meas.aestronglyMeasurable (μ:=prior G f)
       have hh := integral_map hp.aemeasurable (show AEStronglyMeasurable (fun U => g U W) _ from by rwa [hp.map_eq]); rwa [hp.map_eq] at hh
    _ = _ := by
       change (∫ U : Fine, g (Lattice.gauge q U) (Lattice.gauge k V) ∂prior G f)= _
       simp_rw [← show q ∘ S.ratio.embed=k from hm k, hi q]; rfl

lemma cov_section (H : S.patch.Branches S.kernel G) (i : S.Choices) (V : Coarse)
    (o : Site c) (A : Fine → Coarse → ℝ) (ha : Envelope (uncurry A)) (hA : Covariant S A) :
    ∫ a, ticket S β i (F.drape a) (turned o V)*A (F.drape a) (turned o V) ∂F.order G =
    ∫ U : Fine, ticket S β i U V * A U V ∂prior G f := sums_cov S F β H i V o A ha hA

abbrev Drawer (G : Gauge) := Key S × F.Slice G
abbrev All (G : Gauge) := Config G c × Drawer S F G

def base (G : Gauge) : Measure (Drawer S F G) := Measure.count.prod (F.order G)
instance : IsFiniteMeasure (base S F G) := by unfold base; infer_instance
variable (o : Site c)

def stamp (p : All S F G) := ticket S β ((tag S).symm p.2.1) (F.drape p.2.2) (turned o p.1)
def full (G : Gauge) : Measure (All S F G) := fromWeight ((prior G c).prod (base S F G)) (stamp S F β o)
def rootLaw (G : Gauge) : Measure (Config G c) := fromWeight (prior G c) (coarseWeight (G:=G) S β)
abbrev inside (G : Gauge) (V : Config G c) := Middle.conditional (base S F G) (coarseWeight S β) (stamp S F β o) V
abbrev report (f : All S F G → ℝ) (V : Config G c) := Middle.answer (base S F G) (coarseWeight S β) (stamp S F β o) f V

lemma stamp_nn (p : All S F G) : 0 ≤ stamp S F β o p := ticket_nn ..
lemma fullSlice_meas : Measurable (fun p:All S F G => F.drape p.2.2) := by
  let h : Measurable (@Forest.drape _ _ _ F G) := F.continuous_drape.measurable
  exact Measurable.comp (f:=(@Prod.snd (Key S) (F.Slice G)) ∘ (Prod.snd : All S F G → Drawer S F G)) h (measurable_snd.comp measurable_snd)
lemma stamp_env (H : S.patch.Branches S.kernel G) : Envelope (stamp (G:=G) S F β o) := by
  have hu := fullSlice_meas (G:=G) S F
  have hv : Measurable (fun p:All S F G => turned o p.1) := by
    change Measurable (turned o ∘ (Prod.fst : All S F G → Coarse))
    exact (turned_continuous (G:=G) o).measurable.comp measurable_fst
  have hm : Measurable (fun p:All S F G=>p.2.1) := measurable_fst.comp measurable_snd
  unfold stamp
  let P (j:Key S) (p:All S F G) := ticket S β ((tag S).symm j) (F.drape p.2.2) (turned o p.1)
  have hh (j:Key S) : Envelope (P j) := by
    exact ticket_env S β H hu hv ((tag S).symm j)
  let W := envelope_readTag hm (f:=P) hh
  exact W

lemma open_base (A : Key S → F.Slice G → ℝ) (h : Envelope (uncurry A)) :
    (∫ i, A i.1 i.2 ∂base S F G) = ∑ j, ∫ a, A (tag S j) a ∂F.order G := by
  change (∫ i, uncurry A i ∂Measure.count.prod (F.order G))=_
  rw [integral_prod _ (h.integrable _), integral_count]
  exact ((tag S).sum_comp (fun i=> ∫ a, A i a ∂F.order G)).symm

lemma bothLaw (H : S.patch.Branches S.kernel G) : Middle (prior G c) (base S F G)
    (coarseWeight S β) (stamp S F β o) := by
  refine ⟨stamp_env S F β o H,fun i=> stamp_nn ..,coarse_weight_pos S β H,fun i=>?_,coarse_total S β H⟩
  rw [coarse_income S β H]
  let A (j : Key S) (a : F.Slice G) := stamp S F β o (i,(j,a))
  have he : Envelope (uncurry A) := envelope_section (stamp S F β o) (stamp_env S F β o H) i
  change (∫ j, A j.1 j.2 ∂base S F G)=_
  rw [open_base S F A he]
  apply Finset.sum_congr rfl; intro j _
  simpa only [A,stamp,Equiv.symm_apply_apply,mul_one] using cov_section S F β H j i o (fun _ _=>1) (Envelope.const _) (fun _ _ _=> rfl)
lemma full_prob (H : S.patch.Branches S.kernel G) : IsProbabilityMeasure (full S F β o G) :=
  (bothLaw S F β o H).both
lemma root_prob (H : S.patch.Branches S.kernel G) : IsProbabilityMeasure (rootLaw S β G) := by
  obtain ⟨F⟩ := Tree.select S.ratio S.patch.odd_side
  exact (bothLaw S F β 0 H).marginal

end YM.MatchingR2.Top
