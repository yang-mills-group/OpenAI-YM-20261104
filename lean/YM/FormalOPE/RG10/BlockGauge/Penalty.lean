import YM.FormalOPE.RG10.BlockGauge.Prediction
/-!
 # The *actual nonlinear* unmasked formal construction, inflation cost at one genuine step

 Haar normalization & gauge equivariance. For auxiliary diagram prescription costs in Chosen.clear
 chart with any fixed couplings per Work step. `price` same true StepData.kernel prices per
 **independent** quotient edge.Link angles. Producing any relation to real hierarchy away from
 chart not licensed. Background.W. Θ-choice all tags share if using Fk before projecting.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Function Finset PowerSeries Topology Metric Lattice Gauge RG Wilson MeasureTheory
open PertExtension PertExtension.Orb InversionWard Push.Loops
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f n:Side}
variable (S : StepData c f)
variable (H:S.patch.Branches S.kernel G)
variable (t:S.Choices)
local notation "Ω"=> LinkFrame G f
local notation "Ψ"=> LinkFrame G c

lemma along {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E] {x:E}{U:E→ LinkFrame G f} (hu : MatDiffAt U x) : MatDiffAt (fun z => Orb.liftLinks (U z)) x := by intro i; dsimp only; unfold Orb.liftLinks; split; exact hu _; exact mat_inv_diff (hu _)
lemma lift_one : Orb.liftLinks (1: LinkFrame G n)=1 := funext fun i=>by unfold liftLinks; split<;>simp
include H
lemma atStep_smooth {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {x:E}{U:E→ LinkFrame G f} (hu : MatDiffAt U x) (hx: U x=1) : MatDiffAt (fun z => atStep S t (U z)) x:= by
 let v : E→ Push.Loops.Inputs G c f:= fun a=> Sum.elim (Orb.liftLinks (U a)) 1
 have h₁ : v x=1:= by ext1 i; cases i <;> simp [v,hx,lift_one] -- 1 maybe
 have hV: MatDiffAt v x:= fun i=> Sum.recOn (motive:= fun i=> ContDiffAt ℝ ω (fun a=>G.mat (v a i)) x) i (fun k=> along hu k) (fun _=> contDiffAt_const) -- maybe
 have he a : Zmap (S:=S) t (v a)= S.prediction (Orb.liftLinks (U a)) t := by unfold Zmap v; rw [show auxiliaries _= (1:NodeField G c) from rfl,gauge_one]; rfl
 have hm: MatDiffAt (Zmap (S:=S) t ∘ v) x := Zmap_diff H t h₁ hV; unfold MatDiffAt at *; simp_rw [Function.comp_apply,he] at hm; exact fun i=> hm i.val
omit H

-- smooth definite interaction. Coupling multiplier fixed later (no treating β_T as inferred).
-- define cost and numerator noise per edge and exactly normalize.
 def distance (V:LinkFrame G c) := S.kernel.penalty * ∑ i:OEdge c, G.price (V i)
 def penalty (U:LinkFrame G f) (V: LinkFrame G c):= distance S (V*(atStep S t U)⁻¹)
 def heat (β : ℝ) (W:LinkFrame G c) := Real.exp (-β * distance S W)
 def zone (β : ℝ) (c:Side) (f:Side) (G:Gauge) (S:StepData c f): ℝ := (S.penaltyZ β G)^(Fintype.card (OEdge c))

variable (U : LinkFrame G f) (V:LinkFrame G c) (β:ℝ)
lemma heat_count : heat S β V =∏ i, S.penaltyWeight β (V i) := by
 unfold heat distance StepData.penaltyWeight; rw [← mul_assoc,Finset.mul_sum, Real.exp_sum]
@[fun_prop] lemma heat_cont : Continuous (heat S β (G:=G)):= by unfold heat distance; fun_prop
lemma mass : ∫ V:LinkFrame G c, heat S β V ∂(PertExtension.Chart.physical G (OEdge c)) = zone β c f G S:= by
 simp_rw [heat_count]; unfold PertExtension.Chart.physical; rw [integral_fintype_prod_eq_prod (fun (i:OEdge c) v=> S.penaltyWeight (G:=G) β v)]; simp only [Finset.prod_const, Finset.card_univ]; rfl
lemma zone_pos : 0 < zone β c f G S:= pow_pos (S.penaltyZ_pos _) _
lemma heating : ∫ V:LinkFrame G c,Real.exp (-β * penalty S t U V) ∂(PertExtension.Chart.physical G (OEdge c))= zone β c f G S := by
 let v:= (atStep S t U)⁻¹
 let L:=PertExtension.Chart.physical G (OEdge c)
 have hu:MeasurePreserving (fun a:LinkFrame G c=>a*v) L L:= measurePreserving_pi _ _ (fun i=> measurePreserving_mul_right (G.probHaar) (v i)) -- coe syntax
 exact (hu.integral_comp (f:=fun a:LinkFrame G c=>a*v) (Homeomorph.mulRight v).measurableEmbedding (heat S (G:=G) β)).trans (mass S β)
lemma rootEven (p:Site f→ G.El) (h: evenAt p): evenAt (n:=c) (p ∘ S.ratio.embed):=fun x=> by change p (S.ratio.root (-x))=p _; rw [map_neg]; exact h _ -- unused H
include H
lemma motion (p:Site f→ G.El) (h:evenAt p) : penalty S t (even_spin p U) (even_spin (p ∘ S.ratio.embed) V)= penalty S t U V := by
 unfold penalty; rw [step_gauge S H]; unfold distance;
 · congr 1; refine sum_congr rfl fun i _=> ?_; unfold even_spin; simp_rw [Pi.mul_apply,Pi.inv_apply,Lattice.gauge, lift_at]
   set v:= p∘S.ratio.embed; conv_rhs=> rw [← G.price_conj (v i.val.1)]
   congr 1; group
 · exact h
-- choice law of this aux regulator if desired retain exact conditional.Step call all factors using same tag & normalization.
-- No claim of equality to *physical regulator elsewhere*.
end YM.FormalOPE.RG10.BlockGauge
