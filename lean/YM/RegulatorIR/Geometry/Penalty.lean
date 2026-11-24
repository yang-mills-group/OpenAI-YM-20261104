import YM.RegulatorIR.Geometry.Guess
import YM.RegulatorIR.Geometry.End

/-! Haar mass and positivity through a block. Comparison uses this extension
of the formal step law at fixed regulator, arbitrary positive coupling scale on
each step. Doesn't infer a physical law. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Function Set Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Field RG Push Precision
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f:Side}(S:StepData c f) {G:Gauge}

def trouble (S:StepData c f)(V W:spins G c):ℝ := S.kernel.penalty * ∑ i:OEdge c, G.price (V i*(W i)⁻¹)
def bond (U:spins G f)(V:spins G c):ℝ := trouble S V (predictor S U)
lemma goat_fee (V W:spins G c)(k:Site c→ G.El): trouble S (goat k V) (goat k W)=trouble S V W:=by
 unfold trouble; apply congr_arg;apply Finset.sum_congr rfl; intro i _
 rw [goat_at, goat_at,show k i.val.1 * _ * _ * (k i.val.1 * _ * _)⁻¹=k i.val.1*(V i*(W i)⁻¹)*(k i.val.1)⁻¹ by group, G.price_conj]
lemma trouble_cont : Continuous (fun y:spins G c×spins G c=> trouble S y.1 y.2):= by unfold trouble; fun_prop
lemma trouble_nonneg (V W:spins G c):0≤trouble S V W:= mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg (fun _ _=>(G.price_range ..).1))
lemma bond_nonneg (U:spins G f)(V:spins G c):0≤ bond S U V:= trouble_nonneg ..
lemma price_cancel {v:G.El}(h:G.price v=0):v=1:=by
 have ht:= G.chord_price v; rw [h,mul_zero] at ht; have hh:G.chord v=0:=by nlinarith [ht]
 apply G.mat_injective
 unfold Gauge.chord at hh;rw [div_eq_zero_iff] at hh; rcases hh with hz|hz
 · rw [norm_eq_zero,sub_eq_zero] at hz; exact hz
 exact (Real.sqrt_pos.2 (show (0:ℝ)<G.repDim from by exact_mod_cast G.dimPos)).ne' hz|>.elim
lemma trouble_null (V W:spins G c): trouble S V W=0 ↔ V=W:= by
 constructor
 · intro h; ext1 i; have H:= (mul_eq_zero.mp h).resolve_left S.kernel.penalty_pos.ne'
   exact mul_inv_eq_one.mp (price_cancel ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _=> (G.price_range _).1)).mp H i (Finset.mem_univ _)))
 rintro rfl; simp [trouble]
lemma bond_zero (U:spins G f) (V:spins G c): bond S U V=0 ↔ V=predictor S U:= trouble_null ..
lemma pow_root (V Q:spins G c)(b:ℝ): Real.exp (-b*trouble S V Q) = ∏ i:OEdge c, S.penaltyWeight b (V i*(Q i)⁻¹):=by
 unfold trouble; rw [←mul_assoc,Finset.mul_sum,Real.exp_sum]; rfl
lemma bond_mass (U:spins G f)(b:ℝ): (∫ V,Real.exp (-b*bond S U V) ∂spinsMeasure G c)= (S.penaltyZ b G)^Fintype.card (OEdge c):=by
 unfold bond; let Q:= predictor S U; simp_rw [pow_root]
 let w i v:=S.penaltyWeight b (v * (Q i)⁻¹)
 have he i: (∫ v,w i v ∂ G.probHaar) = S.penaltyZ b G := (measurePreserving_mul_right G.probHaar (Q i)⁻¹).integral_comp ((Homeomorph.mulRight (Q i)⁻¹).measurableEmbedding) (S.penaltyWeight b)
 change (∫ (V:OEdge c→ G.El),∏ i,w i (V i) ∂(shellMeasure G (OEdge c)))=_
 unfold shellMeasure; rw [integral_fintype_prod_eq_prod w];simp_rw [he]; simp

variable (H:S.patch.Branches S.kernel G)
include H
lemma bond_flow (k:Site f→G.El)(hk:compatible k)(U:spins G f) (V:spins G c): bond S (goat k U) (goat (k∘ S.ratio.embed) V)=bond S U V:=by unfold bond; rw [prediction_flow S H _ _ hk,goat_fee]
lemma bond_meas : Measurable (fun q:spins G f×spins G c=> bond S q.1 q.2):= by
 have h : Measurable (fun q:spins G f × spins G c=> (q.2,predictor S q.1)):=measurable_snd.prodMk ((predict_measurable S H).comp measurable_fst)
 change Measurable ((fun x: (spins G c) × (spins G c)=> trouble S x.1 x.2) ∘ fun q : spins G f × spins G c=> (q.2,predictor S q.1)); exact Measurable.comp ((trouble_cont S (G:=G)).measurable) h
lemma flat_glow (k : Site f→ G.El)(hk:compatible k)(U:spins G f)(hv:goat k U=1)(V:spins G c): ContinuousAt (fun q:spins G f×spins G c=>bond S q.1 q.2) (U,V) := by
 let P:= fun q:spins G f×spins G c=> (q.2,predictor S q.1)
 have hp:= (look_flat S H U k hk hv).comp (f:=Prod.fst) (show ContinuousAt _ (U,V) from continuous_fst.continuousAt)
 exact (trouble_cont S (G:=G)).continuousAt.comp (f:=P) (continuous_snd.continuousAt.prodMk hp)

-- Each timer not mass convention; can remove normalizing constants mutually.
lemma price_integrable (b:ℝ)(hb:0 ≤ b): Integrable (fun x: spins G f × spins G c=> Real.exp (-b*bond S x.1 x.2)) ((spinsMeasure G f).prod (spinsMeasure G c)):=by
 apply MeasureTheory.Integrable.of_bound ?_ 1 (Eventually.of_forall ?_)
 · exact (((bond_meas S H).const_mul (-b)).exp).aestronglyMeasurable
 intro x; rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (bond_nonneg ..))
lemma null_here : bond S (1:spins G f) 1=0:= (bond_zero ..).mpr (predict_zero S H).symm
end YM.RegulatorIR.Geometry
