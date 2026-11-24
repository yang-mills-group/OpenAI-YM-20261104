import YM.AllOrder.Docket.Air
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "ξ"=> Aux.scope x
local notation "ζ"=> Clock
open Till Tilt Lantern
-- uniform model input forecast. λ.World width &(Boot.Local frames.Fixed age weights before patch). Purchases.G
-- Brush grant `clump` actual.
variable {C₁ Gc t₁:ℝ}{W':PathData G}{k':ℕ} -- remove side
-- fields.Perch primitive
lemma earns_F (F:Forest S.ratio)(Q:ℕ→Atom G k') (x:Positions (Joint F G))(Z t:ℝ) (he:PaintSupply G j Z)(hp: Charged Q t C₁)(ht:0<t)(hn:‖x‖<1)(hu:Fintype.card (Joint F G)≤ Gc)(hw:1≤Gc)(hv:Fintype.card (Site f)≤Gc) : Brush j (Gc *tollS Gc j (C₁*Uniform.atomCost G Z t j k')) 1 (Extra.Iteration.action Q ∘ fine G F) x:= by
 let M s (i:Site f) y:= ∑' p, (Q p).unmasked (signedFine F y s) i
 let V:=Uniform.atomCost G Z t j k'; let r:=tollS Gc j (C₁*V)
 replace hn:=mem_ball_zero_iff.mpr hn; have hp' : 0 < entryWidth j S.patch.L t:=width_positive ht _ _; have hΛ:= budget_nonneg hp; have hV:0≤V:= atomCost_nn he ht _
 have hh s i : Brush j r 1 (M s i) x := by refine Brush.offer.2 ⟨(label_analytic F _ ht hp s he _ _ hn).of_le le_top,fun l hl=>raises hw hu (mul_nonneg hΛ hV) hl (fun q => ?_)⟩; have hh:=(atom_beacon F s ht hp he x hn i) l hl q; exact hh.trans (mul_le_of_le_one_right (mul_nonneg hΛ hV) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp'.le) (Nat.cast_nonneg _))))
 let T:= (Fintype.card Signed:ℝ); have hT:0<T:=(by unfold T; positivity); have hf := ((Brush.spree (Finset.univ:Finset Signed) _ _ zero_le_one (fun s _=> Brush.spree Finset.univ _ _ zero_le_one (fun i _=> hh s i)))|>.smul T⁻¹); simp only [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_pos.mpr hT).le] at hf; refine hf.climb ?_ le_rfl; rw [show (Fintype.card Signed:ℝ)=T from rfl,inv_mul_cancel_left₀ hT.ne']; exact mul_le_mul_of_nonneg_right hv (hh 1 0).nonneg
variable (W:ι→ Aux.Name G P K u x r k U)
namespace Proper
variable (h:Proper W T)
local notation "Vₚ"=> T.Meter
local notation "Vₘ"=> T.Meter
set_option quotPrecheck false
local notation "R"=> fun (i:ι)(j:Age)=> Step.PlanV.authority (Burn.horizon x) j (Step.PlanV.strengthP (W i).due)
local notation "M"=> fun i=>Body ((W i|>.Vx))
local notation "X"=> fun i => ((W i).X× Body (W i).Vx)
local notation "J"=> (W∘ Sigma.fst) -- no
include h
variable (l:ℕ)
lemma capitulate (Q:∀ i, (W i).X × Body (W i).Vx) (j:Age)(hj:j∈ξ)(he:∀ᶠ i in T.rail, ‖Q i‖ < 1) : Catch.Cover (V:= X) T l 0 (fun _=>1) (fun i=> far (W i).Fs (W i).shape j) Q := by
 obtain ⟨s,hs,hB⟩:=h.legible; obtain ⟨Z,hZ⟩:=paint_supply G l; let C i:= (W i).vol*tollS (W i).vol l ((R i j)*Uniform.atomCost G Z (s j) l j.r)
 have hc: Vₚ C 0:= by unfold C tollS; let hV:=counts W h; exact hV.unitPay le_rfl ((hV.pow l).unitPay (by simp) ((hire W h j).rscale _))
 apply Cover.has hc; filter_upwards [hB,he] with i hi hp; let A:=W i; let a:= combineH A.forest (G:=G); have hv:= feesComb A.forest (G:=G); let u:=A.loom; have H: ‖a (Q i)‖<1:= (le_trans (a.toContinuousLinearMap.le_opNorm _) (mul_le_of_le_one_left (norm_nonneg _) hv)).trans_lt hp; have ht := reading a.toContinuousLinearMap (earns_F A.forest (A.shape j) (a (Q i)) Z _ hZ (hi.handy _ hj|>.pay) (hi.sk j) H u.overall u.one u.finalP) hv; rw [one_mul] at ht; exact ht -- f shape orientation
lemma gas (G0:∀ i,ℝ × ((W i).X × Body (W i).Vx))(hG:∀ᶠ i in T.rail,‖G0 i‖ < 1) : Catch.Cover (V:=fun i=>ℝ × X i) T l 0 (fun _=>1) (fun i=> (W i).Qc) G0:= by
 let Z i:= ContinuousLinearMap.fst ℝ ℝ (X i); let s i:= ContinuousLinearMap.snd ℝ ℝ (X i); have ht: Vₚ (fun i=> ‖G0 i‖) 0:= Clock.Meter.smaller (Clock.Meter.const T 1) (hG.mono (fun i hi=> (abs_of_nonneg (norm_nonneg _)).trans_le (hi.le.trans (le_abs_self _))))
 have hb: Cover T l 0 (fun _=>1) (fun i=> ⇑(Z i)) G0:= by refine (Cover.comp_lin («L»:=Z) (s:=0) ht le_rfl ?_).weak (by simp); exact (Clock.Meter.const T 1).smaller (Eventually.of_forall fun i=> (abs_of_nonneg (norm_nonneg _)).trans_le ((ContinuousLinearMap.norm_fst_le ..|>.trans (le_abs_self _))))
 have hS: Cover (U:= X) T l 0 (fun _=>1) (fun i=> ⇑(s i)) G0:= by refine (Cover.comp_lin (L:=s) (s:=0) ht le_rfl ?_).weak (by simp); exact (Clock.Meter.const T 1).smaller (Eventually.of_forall fun i=> (abs_of_nonneg (norm_nonneg _)).trans_le ((ContinuousLinearMap.norm_snd_le ..|>.trans (le_abs_self _))))
 let f (j:Age)i:= spark (W i).Fs (W i).shape j; have hp (j:Age)(hj:j∈ξ): Cover T l 0 (fun _=>1) (f j) G0:= by
     let G' i:= s i (G0 i); have hh:= (capitulate W h l G' j hj (hG.mono fun i hi=> (norm_snd_le _).trans_lt hi)); unfold f spark; exact ((hb.powerC j.stamp).mul ((Cover.comp (u:=fun i=> far (W i).Fs (W i).shape j) le_rfl hS hh).weak (b:=0) (by simp))).weak (by simp) -- implicit power from mul shape
 rw [show (fun i=> (W i).Qc)=(∑ j∈ξ,f j) from funext fun i=> (Finset.sum_apply i ξ f).symm]; exact Cover.collects _ hp
lemma flooding : Flood (fun i=> (W i).Qc) T l:= by
 refine ⟨Eventually.of_forall fun i=> rise (W i),fun e he=> ?_⟩; let P i := Metric.ball (0:ℝ × ((W i).X × Body (W i).Vx)) 1; let t:=T.book P; let O:= T.bookF P
 have hm := gas (T:=t) (W∘Sigma.fst) (Proper.sail W h _ _ O) l (fun i=> i.2.1) (Eventually.of_forall fun i=> show ‖i.2.1‖<1 from mem_ball_zero_iff.mp i.2.2)
 filter_upwards [T.booked P (fun i x=>Brush l (T.cost i^e) 1 (W i|>.Qc) x)|>.mp (hm e he)] with i hi; exact fun x hx=> hi _ (mem_ball_zero_iff.mpr hx)
end Proper
end Name
end YM.AllOrder.Aux
