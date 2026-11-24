import YM.OPE.Frame.Reading
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
/-!
# Slew the activation of the rows smoothly with their fixed costs (only finitely active)
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector)
local notation "ν" => normalizedRotations
attribute [local instance] YM.Work.A15.compact_ortho
private lemma smooth_angular {E F V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × V → F) {u : Ortho → V} (hu : Continuous u) {s : Set E} (hs : IsOpen s)
    (hh : ∀ (x : E), x ∈ s → ∀ K, ContDiffAt ℝ ∞ f (x, u K)) :
    ContDiffOn ℝ ∞ (fun x=>∫ K : Ortho, f (x,u K) ∂ν) s := by
  rw [contDiffOn_infty]; intro n; induction n generalizing F with | _ => _
  all_goals
    let A (p : E × V) := (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E V)
    have hm (x : E) (h : x ∈ s) (K : Ortho) : ContDiffAt ℝ ∞ A (x,u K) :=
      ((hh x h K).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_comp contDiffAt_const -- use notation `∞` WithTop ℕ∞? likely ∞ elaborator
    have he (x : E) (h : x∈s) : HasFDerivAt (fun x=>∫ K : Ortho, f (x,u K) ∂ν) (∫ K : Ortho, A (x,u K) ∂ν) x := by
      obtain ⟨ε,hε,hx⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds h)
      let t := Metric.closedBall x (ε/2); have ht : t ⊆ s := Subset.trans (Metric.closedBall_subset_ball (half_lt_self hε)) hx
      have ha (x:E) (h:x∈s) : Continuous (fun K=> f (x, u K)) := continuous_iff_continuousAt.mpr fun K => (hh x h K).continuousAt.comp (f:=fun K=> (x,u K)) (continuousAt_const.prodMk hu.continuousAt)
      have hf : ContinuousOn (fun p : E × Ortho=> ‖A (p.1, u p.2)‖) (t ×ˢ univ) := fun p hp =>
        (((hm p.1 (ht hp.1) p.2).continuousAt.norm).comp (f:=fun p:E×Ortho=> (p.1,u p.2)) (continuous_fst.prodMk (hu.comp continuous_snd)).continuousAt).continuousWithinAt
      obtain ⟨B,hB⟩ := (((isCompact_closedBall ..).prod isCompact_univ).image_of_continuousOn hf).bddAbove
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds x (half_pos hε)) (Eventually.mono (p:=fun x=>x∈s) (hs.mem_nhds h) <| fun x h => (integralable (ha x h)).aestronglyMeasurable) (integralable (ha x h)) ?_
        (Eventually.of_forall fun K x h=> hB ⟨(x,K),⟨h,mem_univ _⟩,rfl⟩) (integrable_const B) ?_
      · exact (integralable (continuous_iff_continuousAt.mpr fun K => (hm x h K).continuousAt.comp (f:=fun K=> (x,u K)) (continuousAt_const.prodMk hu.continuousAt))).aestronglyMeasurable
      exact Eventually.of_forall fun K x h => ((hh x (ht h) K).differentiableAt (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (u K))
  case zero => exact contDiffOn_zero.mpr (fun x hx=> (he x hx).continuousAt.continuousWithinAt)
  case succ n ih _ _ _ =>
    rw [Nat.cast_succ,contDiffOn_succ_iff_fderiv_of_isOpen hs]; refine ⟨fun x hx=> (he x hx).differentiableAt.differentiableWithinAt, by simp, (ih A hm).congr fun x hx=>(he x hx).fderiv⟩

variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S} {X : Rotation S} {ρ : S.RealSpin}
    {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {o : E4} {d : ℕ} (D : Detector S d)
private def clearance : ℝ := (MultipleContact.detector_clearance D).choose
/-- Tail budget for the probe at this grade. -/
def threshold : ℝ := min (clearance D) ((d+1:ℝ)⁻¹)
lemma threshold_positive : 0 < threshold D := lt_min (MultipleContact.detector_clearance D).choose_spec.1 (inv_pos.mpr (by positivity))
lemma cleared {x : I → E4} (h : Injective x) (hz : ∀ i, ‖x i-o‖ < 2 * threshold D) : admissible D x o := by
  intro e K; refine beside_distinct.mpr ⟨h, (beside_distinct.mp (escorts_head e.val o K)).2.1,fun i j hj=>?_⟩
  have hp : 2 * clearance D ≤ ‖bearing e.val j‖ := (MultipleContact.detector_clearance D).choose_spec.2 e.val e.property j
  apply not_lt_of_ge ((mul_le_mul_of_nonneg_left (show threshold D ≤ clearance D from min_le_left ..) zero_le_two).trans hp) ?_; specialize hz i; rw [hj,escorts,add_sub_cancel_right,Ortho.move_norm] at hz; exact hz
lemma within_reach (h : Injective x) (b : ℝ) (hb : b ≤ threshold D) (ha : ∀ i, ‖x i-o‖ ≤ b) : admissible D x o := cleared D h fun i => (ha i).trans_lt (lt_of_le_of_lt hb (by linarith only [threshold_positive D]))

/-- Declared common domain of use, every row. Large enough for all fixed compact O(r) footprints,
whatever the internal geometry. (On this domain, *active* detector demands will fit.) Uses cube of
all positions and true Euclidean norms. -/
structure Seen (r : ℝ) (x : I → E4) (o : E4) : Prop where
  radius : 0 < r
  housed (i : I) : ‖x i-o‖ < Real.sqrt r
  separated : Injective x

/-- `.gate` depends only on the declared scale (and row grade), not on the word or shape;
easier when nesting. It is identically 1 in the germ through each fixed row simultaneously
for all geometries. -/
def gate (r : ℝ) : ℝ := Real.smoothTransition (2 - 2*r/(threshold D)^2)
lemma switched {r : ℝ} (hr : ¬ r < (threshold D)^2) : gate D r = 0 := Real.smoothTransition.zero_of_nonpos (by
  rw [sub_nonpos,le_div_iff₀ (pow_pos (threshold_positive D) _)]; nlinarith [le_of_not_gt hr])
lemma activated : ∀ᶠ r in 𝓝[>] 0, gate D r = 1 := by
  refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
  filter_upwards [gt_mem_nhds (show 0 < (threshold D)^2 / 2 by positivity [threshold_positive D])] with i hi
  apply Real.smoothTransition.one_of_one_le; have he : 2*i/(threshold D)^2 ≤ 1 := (div_le_one (pow_pos (threshold_positive D) _)).mpr (by linarith only [hi]); linarith only [he]
lemma gate_smooth : ContDiff ℝ ∞ (gate D) := Real.smoothTransition.contDiff.comp ((by fun_prop) : ContDiff ℝ ∞ (fun r:ℝ=> 2 - 2*r/(threshold D)^2))
lemma gate_fitted {r : ℝ} (hr : r ≤ (threshold D)^2) (hx : Seen r x o) : admissible D x o :=
  within_reach D hx.separated _ ((Real.sqrt_le_left (threshold_positive D).le).mpr hr) (fun i => (hx.housed i).le)
lemma eventually_dark (A : ∀ d, Detector S d) (r : ℝ) (hr : 0 < r) : ∀ᶠ n in atTop, gate (A n) r = 0 := by
  have ht : Tendsto (fun n:ℕ=> ((n:ℝ)+1)⁻¹ ^ 2) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop)).pow 2; simpa using ht
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with n hn using switched (A n) (not_lt.mpr (((pow_le_pow_left₀ (threshold_positive _).le (min_le_right ..) _)).trans (show _ ≤ r from hn.le)))

lemma assess_at (hX : X.Laws P ρ) (h : S.Hierarchy) (A : I → S.Tag)
    (he : Injective x) (hi : ∀ i, ‖x i-o‖ < 2*threshold D) : ContDiffAt ℝ ∞ (fun p : (I→E4) × E4 => assess X ρ D p.1 A p.2) (x,o) := by
  let T := {p : (I → E4) × E4 | Injective p.1 ∧ ∀ i, ‖p.1 i - p.2‖ < 2 * threshold D}
  have hx : (x,o)∈T := ⟨he, hi⟩; have ht : IsOpen T := by
    have he : IsOpen {x : I → E4 | Injective x} := by
      rw [show {x:I→E4| Injective x}=(fun x:I→E4=>points (x ∘ runNames I)) ⁻¹' conf _ from Set.ext fun x=> runs_conf.symm]; exact (conf_open _).preimage (by unfold points; fun_prop)
    refine (he.preimage continuous_fst).inter ?_
    have hf : {p : (I→E4)×E4|∀ i, ‖p.1 i - p.2‖ < 2*threshold D} = ⋂ i:I, {p : (I→E4)×E4 | ‖p.1 i - p.2‖ < 2*threshold D} := ext fun i => by simp
    change IsOpen {p : (I→E4)×E4|∀ i, ‖p.1 i - p.2‖ < 2*threshold D}; rw [hf]; exact isOpen_iInter_of_finite fun i:I=> isOpen_lt (by fun_prop) continuous_const
  have hw (b : Bool) : ContDiffOn ℝ ∞ (fun p : (I→E4)×E4 => investigate X ρ D b p.1 A p.2) T := by
    refine ContDiffOn.sum ?_; intro e _
    let C := Fin e.val.n → E4
    let n (i : Fin e.val.n) := (e.val.letter i).fst
    let W := ∀ i, S.Field (n i)
    let u (K : Ortho) : (C × W) × S.Field d := ((Ortho.move K ∘ bearing e.val, readAs X ρ e.val b K), rotatedAnswer X ρ D e b K)
    let φ (p : ((I → E4) × E4) × (C × W) × S.Field d) : S.Field d :=
      sense S (beside p.1.1 (fun i=> p.2.1.1 i + p.1.2)) (beside A (fun i=> ⟨n i,p.2.1.2 i⟩)) • p.2.2
    have hu : Continuous u := Continuous.prodMk (Continuous.prodMk (continuous_pi fun i=>rotate_cont _) (continuous_pi fun i=>hX.spin _ _)) (hX.spin d _)
    refine smooth_angular φ hu ht ?_; intro p hp K
    let f (q : ((I→E4)× E4) × (C × W) × S.Field d) : ((I⊕Fin e.val.n → E4) × W) := (beside q.1.1 (fun i=> q.2.1.1 i+q.1.2), q.2.1.2)
    have hf : ContDiff ℝ ∞ f := by
      refine ContDiff.prodMk (contDiff_pi.mpr (fun i=> ?_)) (contDiff_snd.comp (contDiff_fst.comp contDiff_snd)); rcases i with i|i
      · exact (contDiff_apply ℝ E4 i).comp (contDiff_fst.comp contDiff_fst) -- syntax
      show ContDiff ℝ ∞ (fun p : ((I→E4)×E4) × (C×W) × S.Field d=> p.2.1.1 i + p.1.2); exact ((contDiff_apply ..).comp (contDiff_fst.comp (contDiff_fst.comp contDiff_snd))).add (contDiff_snd.comp contDiff_fst)
    exact ((sense_vary_ext_smooth (n:=n) A h.smooth _ (cleared D hp.1 hp.2 e K)).comp (p,u K) hf.contDiffAt).smul (contDiffAt_snd.comp _ contDiffAt_snd)
  exact (((hw false).contDiffAt (ht.mem_nhds hx)).add ((hw true).contDiffAt (ht.mem_nhds hx))).const_smul _
end YM.OPE.Frame
