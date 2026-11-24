import YM.OPE.Compatible.Zephyr.Gust
import YM.OPE.Compatible.Rail.Track
/-! # e geometric overview -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
variable {N:ChartRatio G}(hN:LocalRatio N){t r R B b:ℝ}
variable {S:StepData c f}{F:Forest S.ratio}(I: Seats F)
noncomputable def stake :Keys G (↥I)→L[ℝ] AxisChart G F:= ContinuousLinearMap.pi fun i=> if h:i∈I then ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:↥I=>G.Color) ⟨i,h⟩ else 0
@[simp] lemma stake_on (i:↥I)(p: Keys G (↥I)): stake I p i.val=p i:=by unfold stake; rw [ContinuousLinearMap.pi_apply, dif_pos i.property]; rfl
lemma stake_off (p: Keys G (↥I))(i:F.Free)(h:i∉I): stake I p i=0:=by unfold stake; rw [ContinuousLinearMap.pi_apply,dif_neg h]; rfl
lemma firmly (p: Keys G (↥I)): ‖stake I p‖=‖p‖:=by
       refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_)
       · intro i; by_cases h:i∈I
         · rw [show stake I p i=_ from stake_on I ⟨i,h⟩ p]; exact norm_le_pi_norm ..
         rw [stake_off I p i h,norm_zero]; exact norm_nonneg _
       intro i; rw [←stake_on I i p]; exact norm_le_pi_norm ..
variable (J:Seats F)(x:World F J G) (v:AxisChart G F)
abbrev Stowed (v:AxisChart G F):Prop:=∀ i∈I,v i=0
def Poured (v:AxisChart G F)(t:ℝ):Prop:= Stowed I v ∧ ald I J x= fun i=> put (t • v) i.val
variable {I J v x}
lemma hiss (hv:Poured I J x v t)(p:Keys G (↥I)): Wind I (put (t • p)) (ald I J x)=put (t • (v+stake I p)):=by
       ext1 i; by_cases h:i∈I
       · let j:↥I:=⟨i,h⟩; rw [show Wind I (put (t • p)) (ald I J x) i= put (t • p) j from congr_fun (interior_e I _ _) j]; change _= G.lieExp (t • (v i+stake I p i)); rw [hv.1 i h,zero_add,show stake I p i=p j from stake_on I j p]; rfl
       rw [exterior_e I (put (t • p)) (ald I J x) ⟨i,h⟩]; rw [hv.2]; change _= G.lieExp (t • (v i+stake I p i)); rw [stake_off I p i h, add_zero];rfl
variable (H:Sweep N r R)
include H in
lemma grazed {t:ℝ}(hy:I⊆J)(hx:dazed hy b B x)(hp:0 ≤ b)(hh:b≤ R)(ht:0<t):∃ v,Poured I J x v t ∧ (∀ i∉J,v i=0) ∧ ‖v‖ ≤2*b/t:=by
    have hv(i:F.Free):∃ z:G.Color,(i∉I→ i∈ J → ∀ j:i∉I, put (I:=F.Free) (fun _=> t • z) i=ald I J x ⟨_,j⟩)∧ (i∈I∨i∉J→z=0) ∧ ‖z‖≤2*b/t:=by
         by_cases h:i∈I∨i∉J; · exact ⟨0,fun hx ht _=>False.elim (Or.elim h (fun h=>hx h) fun h=>h ht),fun _=>rfl,norm_zero.trans_le (by positivity)⟩
         push Not at h; obtain ⟨z,hz,he⟩:= H.acts (show x ⟨i,h.2⟩∈ G.shell R from (hx.2 _ h.1).trans hh); refine ⟨t⁻¹ • z,fun _ _ j=> ?_,fun hg => False.elim (Or.elim hg (fun hh=>h.1 hh) fun hh=> hh h.2),?_⟩
         · unfold ald put Chart.expLinks; rw [smul_inv_smul₀ ht.ne',he]; rw[dif_pos h.2]
         rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le),← div_eq_inv_mul, div_le_div_iff_of_pos_right ht]; have ht: ‖z‖/2≤ b:=(H.price z hz).1.trans (he.symm ▸ (hx.2 _ h.1)); linarith
    choose z H H' h using hv
    refine ⟨z,⟨fun i hi=>H' i (Or.inl hi), funext fun i=>?_⟩,(fun i hi=>H' i (Or.inr hi)),(pi_norm_le_iff_of_nonneg (by positivity)).2 h⟩; by_cases hk:i.val∈J
    · exact (H _ i.property hk i.property).symm
    unfold ald put Chart.expLinks; rw [dif_neg hk,Pi.smul_apply,H' i.val (Or.inr hk), smul_zero,G.mat_lieExp_zero]
open Flume.Virgin
variable (P:Rep G f)(w: Bid.Dir G c)(k:S.Choices)
set_option quotPrecheck false
local notation "Tμ"=> Chart.tangent G (↥I)
local notation "PX"=> P.path
local notation "YP"=> pane F k P.clip PX
local notation "M"=> Module.finrank ℝ (Keys G (↥I))
-- subtract rest_0 instead of ext; allow additive μ global computed near patch.
abbrev ScoreV (F:Forest S.ratio) (I:Seats F) (P:Rep G f)(k:S.Choices)(v:AxisChart G F)(w: Bid.Dir G c)(t:ℝ)(p: Keys G (↥I)):=
     -(P.beta*(pane F k P.clip P.path (t • (w,v+stake I p))- pane F k P.clip P.path 0)) - (springF F P.path (t • (v+stake I p))-springF F P.path 0)
abbrev Rotary (w: Bid.Dir G c)(t:ℝ) (F:Forest S.ratio) (I:Seats F)(k:S.Choices) (P:Rep G f)(v:AxisChart G F)(N:ChartRatio G)(p:Keys G (↥I)):= Real.exp (feeX N (t • p)+ScoreV F I P k v w t p)
variable {k P}
-- integral equality (nonzero denomin assumed later)
--variable (H)
local notation "SL"=> CapeQ G (↥I) B t r
local notation "Qx"=> Arbor (represent (t • w)) P k I J B x
include hN H
lemma dataV (hp:Poured I J x v t)(hR:B ≤ R)(ht:0<t)
      (f:World F I G→ℝ)(hg:Measurable (Qx*f)) : (∫ p,(Qx*f) p ∂hail G I)=
 t^M * (N.scale ^ (Fintype.card (↥I)) * Real.exp (-(ScoreV F I P k v w t 0))) *∫ p in SL, Rotary w t F I k P v N p * f (put (t • p)) ∂Tμ:=by
          have hz : Bravo P (represent (t • w)) k ∘ (fun p:Keys G (↥I)=> F.drape (Wind I (put (t • p)) (ald I J x)))= fun p=> P.beta*(YP (t • (w,v+stake I p))) + springF F PX (t • (v+stake I p)) :=funext (fun p=>by rw [Function.comp_apply,hiss hp];rfl)
          let L:= ScoreV F I P k v w t; let A:= N.scale ^ (Fintype.card (↥I)) * Real.exp (-(L 0)); have hp'(p:Keys G (↥I))(hh:p∈ SL) : Chart.jacobian N (t • p)* ((Qx*f) (put (t • p)))= A * (Rotary w t F I k P v N p *f (put (t • p))):=by
               have he : Qx (put (t • p))= Real.exp (L p-L 0):=by unfold Arbor; rw [if_pos (show Shelter I B (put (t • p)) from hh.1)]; apply congr_arg Real.exp; unfold tweak; rw [draped,resetting,show (1:World F I G)=put (t• (0:Keys G (↥I))) from by rw [smul_zero,put_zero]]; rw [show Bravo _ _ _ _=_ from congr_fun hz p, show Bravo _ _ _ _=_ from congr_fun hz 0]; unfold L ScoreV;ring
               rw [pay hN H (t • p) hh.2,Pi.mul_apply,he]; unfold A L Rotary; rw [Real.exp_sub,Real.exp_add,Real.exp_neg]; ring
          have hZ:= giving hN H (Qx * f) hg (fun i hi=>by unfold Arbor; rw [Pi.mul_apply,if_neg (show ¬Shelter I B i from hi),zero_mul]) hR ht
          rw [show (∫ p,(Qx*f) p ∂hail G I) =_ from hZ, mul_assoc]; apply congr_arg (t^M*·); rw [← integral_const_mul]; exact setIntegral_congr_fun capeMeas hp'
lemma summit (hp:Poured I J x v t)(hR:B ≤ R)(ht:0<t)(hx:Measurable (Qx))
      (f:World F I G→ℝ)(hg:Measurable (Qx*f)) : Rails P (represent (t • w)) k I J B x f=
 (∫ p in SL, Rotary w t F I k P v N p * f (put (t • p)) ∂Tμ)/(∫ p in SL, Rotary w t F I k P v N p ∂Tμ):=by
      rw [show Rails P (represent (t • w)) k I J B x f=(∫ p,(Qx*f) p ∂hail G I) / (∫ p,(Qx * 1) p ∂hail G I) from by rw [mul_one];rfl, dataV hN H w hp hR ht _ hg, dataV hN H w hp hR ht _ (by rwa [mul_one])]; simp_rw [Pi.one_apply, mul_one]; apply mul_div_mul_left; exact mul_ne_zero (pow_pos ht _).ne' (mul_pos (pow_pos hN.scale _) (Real.exp_pos _)).ne' -- maybe _root
end YM.OPE.Zeph
