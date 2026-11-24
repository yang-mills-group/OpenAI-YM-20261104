import YM.FormalOPE.RG10.BlockGauge.Expenses
/-!
 # Noise transformation for seeing what genuine `StepData` rules do to whole diagrams.

 Cost-scheduling built later. `dry` extracts group-valued noises; `rain`
 reconstructs all configurations and their interaction penalties.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
namespace Fabric
variable (L : Fabric G n)
abbrev Clouds:= L.More→ G.El
 def runoff (u:L.LinksOn): L.Clouds:= u∘ Sum.inr
 def combine (u:LinkFrame G n)(y:L.Clouds) : L.LinksOn := Sum.rec (motive:=fun _=>G.El) u y
@[fun_prop] lemma runoff_cont : Continuous (L.runoff):= continuous_pi fun _=> continuous_apply _
@[fun_prop] lemma combine_cont : Continuous (uncurry L.combine):= by
 apply continuous_pi; intro i; cases i
 · rename_i i; exact (continuous_apply i).comp continuous_fst
 rename_i i; exact (continuous_apply i).comp continuous_snd
@[simp] lemma principal_comb (u:LinkFrame G n)(y:L.Clouds) : L.principal (L.combine u y)=u:=rfl
@[simp] lemma runoff_comb (u:LinkFrame G n)(y:L.Clouds): L.runoff (L.combine u y)=y:=rfl
@[simp] lemma comb_principal (u:L.LinksOn): L.combine (L.principal u) (L.runoff u)=u:= funext fun i=> by cases i<;>rfl
lemma comb_one : L.combine 1 1=1:= L.comb_principal (1:L.LinksOn)
lemma together (u y u' y') (h:u=u') (i:y=y'): L.combine u y=L.combine u' y':= by rw [h,i]

variable (S:StepData c f)(B:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val)(L':Fabric G c)
 def dry {n}(L:Fabric G n)(u:LinkFrame G n)(y:L.Clouds) : L.Clouds:=
 match L with
 | .endcap _ _=> y
 | .layer S _ t _ L => L.combine (L.principal y * (atStep S t u)⁻¹) (dry L (L.principal y) (L.runoff y))
 def rain {n}(L:Fabric G n)(u:LinkFrame G n)(e:L.Clouds): L.Clouds:=
 match L with
 | .endcap _ _=> e
 | .layer S _ t _ L =>
     let b:= L.principal e * atStep S t u
     L.combine b (rain L b (L.runoff e))
local notation "Γ" => layer S B t hf L'
lemma dry_eq (u)(w: L'.LinksOn) : (Γ).dry u w = L'.combine (L'.principal w * (atStep S t u)⁻¹) (dry L' (L'.principal w) (L'.runoff w)):= by rw [dry]
lemma rain_eq (u)(w:L'.LinksOn): (Γ).rain u w=L'.combine (L'.principal w * atStep S t u) (rain L' (L'.principal w * atStep S t u) (L'.runoff w)):= by rw [rain]

lemma dry_rain {n}(L: Fabric G n)(u) (w): L.dry u (L.rain u w)=w:= by
 cases L with
 | endcap => rfl
 | layer S _ t _ L =>
   change L.LinksOn at w
   rw [rain_eq,dry_eq,principal_comb,runoff_comb,mul_inv_cancel_right,dry_rain L,comb_principal]
termination_by structural L
lemma rain_dry {n}(L: Fabric G n)(u) (w): L.rain u (L.dry u w)=w:= by
 cases L with
 | endcap => rfl
 | layer S _ t _ L =>
    change L.LinksOn at w
    rw [dry_eq,rain_eq,principal_comb,runoff_comb,inv_mul_cancel_right,rain_dry L,comb_principal]
termination_by structural L
lemma rain_one {n} (L: Fabric G n): L.rain 1 1=1:= by
 cases L with
 | endcap => rfl
 | layer S B t _ L=>
    change L.combine (1*atStep S t 1) (L.rain (1*atStep S t 1) 1)=1
    rw [unit_step S B t,one_mul,rain_one L]; exact comb_one L
termination_by structural L
lemma dry_one : L.dry 1 1=1:= by nth_rw 1 [← L.rain_one]; rw [dry_rain]

-- measure calculus. defEq for instances may be sticky. tolerate.S.
@[fun_prop] lemma leftMeas {n}(L:Fabric G n): Measurable (uncurry L.dry):= by
 cases L with
 | endcap => exact measurable_snd
 | layer S B t hf L =>
     have hz : Measurable (@Prod.fst (LinkFrame G n) L.LinksOn):= measurable_fst
     have hu : Measurable (@Prod.snd (LinkFrame G n) L.LinksOn):= measurable_snd
     have F:= (principal_cont L).measurable.comp hu
     have H:= (runoff_cont L).measurable.comp hu
     exact L.combine_cont.measurable.comp ((F.mul ((atStep_meas S B t).comp hz).inv).prodMk ((leftMeas L).comp (F.prodMk H))) -- `fn wildcard`
termination_by structural L
@[fun_prop] lemma rightMeas {n}(L:Fabric G n): Measurable (uncurry L.rain):= by
 cases L with
 | endcap => exact measurable_snd
 | layer S B t hf L =>
    have hz : Measurable (@Prod.fst (LinkFrame G n) L.LinksOn):= measurable_fst
    have hu : Measurable (@Prod.snd (LinkFrame G n) L.LinksOn):= measurable_snd
    have hb:= ((principal_cont L).measurable.comp hu).mul ((atStep_meas S B t).comp hz)
    have hc:= (runoff_cont L).measurable.comp hu
    exact L.combine_cont.measurable.comp (hb.prodMk ((rightMeas L).comp (hb.prodMk hc)))
termination_by structural L
 def drizzle (u:LinkFrame G n): L.Clouds≃ᵐL.Clouds where
  toFun:= L.dry u
  invFun:= L.rain u
  left_inv:=L.rain_dry u
  right_inv:= L.dry_rain u
  measurable_toFun := L.leftMeas.of_uncurry_left -- expects param?
  measurable_invFun := L.rightMeas.of_uncurry_left
end Fabric
end YM.FormalOPE.RG10.BlockGauge
