import YM.FormalOPE.RG10.Inherit.Booth
/-!
 # Getting Hessian/unique compact minimum from the top + independent noise factors
 Connect Reference bookkeeping to true `L.price` slots & schedule in Section.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {E I J:Type}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable {x:E}
lemma extend (f:I→ J) {u:E→Configuration G J}(hu:MatDiffAt u x): MatDiffAt (fun i=> u i ∘ f) x:= fun i=> hu (f i)
lemma mult {u v:E→Configuration G I}(ha:MatDiffAt u x)(hb:MatDiffAt v x): MatDiffAt (fun t=> u t * v t) x:= by intro i; simp only [Pi.mul_apply,G.mat_mul]; exact (ha _).mul (hb _)
lemma invert {u:E→Configuration G I}(h:MatDiffAt u x): MatDiffAt (fun t=> (u t)⁻¹) x:= fun i=> mat_inv_diff (h i)

variable {f : Side}(L:Fabric G f) {u:E→LinkFrame G f} {v:E→L.Clouds}
lemma union_form {u v}(hu: MatDiffAt u x)(hv: MatDiffAt v x): MatDiffAt (fun t=> L.combine (u t) (v t)) x:= by
 intro i; cases i with
 | inl i=> exact hu i
 | inr i=> exact hv i
lemma crest_form (h: MatDiffAt u x)(H:MatDiffAt v x)(ha:u x=1)(hb:v x=1): MatDiffAt (fun t=> L.dry (u t) (v t)) x:= by
 -- induction. Need declare L etc explicit
 induction L with
 | endcap=> exact H
 | @layer c f S B k hf L ih=>
   let D:=Fabric.layer S B k hf L
   let V:=v
   let s:=L.principal ∘ V
   have he:s x=1:= by unfold s V; rw [Function.comp_apply,hb]; rfl
   let p:=L.runoff ∘ V
   have hi:p x=1:=by unfold p V; rw [Function.comp_apply,hb]; rfl
   have h₁:MatDiffAt s x:= extend Sum.inl H
   have h₂:MatDiffAt p x:= extend Sum.inr H
   exact union_form L (mult h₁ (invert (atStep_smooth S B k h ha))) (ih h₁ h₂ he hi)
lemma woke_form (h: MatDiffAt u x)(H:MatDiffAt v x)(ha:u x=1)(hb:v x=1): MatDiffAt (fun t=> L.rain (u t) (v t)) x:= by
 induction L with
 | endcap=> exact H
 | @layer c f S B k hf L ih=>
    let s:= fun a=> L.principal (v a)*atStep S k (u a)
    have he:s x=1:= by unfold s; rw [ha,hb,unit_step S B k]; change (1:LinkFrame G c)*1=_; simp
    have h₁:MatDiffAt s x:= mult (extend Sum.inl H) (atStep_smooth S B k h ha)
    let p:= fun a=> L.runoff (v a)
    have hi:p x=1:=by unfold p; rw [hb]; rfl
    have h₂:MatDiffAt p x:= extend Sum.inr H
    exact union_form L h₁ (ih h₁ h₂ he hi)

lemma deck_shape {u:E→Configuration G (Orb.Cotree f)} (h:MatDiffAt u x): MatDiffAt (fun t=> deck (u t)) x:= by
 intro i; dsimp only [deck]; unfold Orb.splitLink; split
 · exact contDiffAt_const
 exact h _
lemma deck_cont : Continuous (deck (G:=G) (f:=f)):= by apply continuous_pi; intro i; unfold deck Orb.splitLink; split<;>fun_prop
lemma key_meas:Measurable (key L):= deck_cont.measurable.comp (f:=fun x:Configuration G (Reference L)=> x ∘ Sum.inl) (measurable_pi_lambda _ (fun _=>measurable_pi_apply _)) -- syntax f not p
lemma key_form {u:E→Configuration G (Reference L)}(h:MatDiffAt u x): MatDiffAt (key L ∘ u) x:= deck_shape (extend Sum.inl h)
lemma key_one: key L 1=1:= by unfold key deck; ext1 i; unfold Orb.splitLink; split<;>rfl

abbrev Booth:= Configuration G (Reference L)
 def dried (u:Booth L): Booth L:= Sum.elim (u ∘ Sum.inl) (L.dry (key L u) (u∘Sum.inr))
 def woke (u:Booth L): Booth L:= Sum.elim (u ∘ Sum.inl) (L.rain (key L u) (u∘Sum.inr))

def attune (L: Fabric G f) : Atelier G (Reference L) (Reference L) where
 placement:={
   toFun:=dried L
   invFun:=woke L
   left_inv u:= by
     ext1 i; cases i
     · rfl
     rename_i i; exact congr_fun (L.rain_dry (key L u) (u∘Sum.inr)) i
   right_inv u:= by
     ext1 i; cases i
     · rfl
     rename_i i; exact congr_fun (L.dry_rain (key L u) (u∘Sum.inr)) i
   measurable_toFun:= by
     apply measurable_pi_lambda; intro i; cases i
     · exact measurable_pi_apply _
     rename_i i
     exact ((measurable_pi_apply _).comp L.leftMeas).comp ((key_meas L).prodMk (show Measurable (fun u:Booth L=> u ∘ Sum.inr) from measurable_pi_lambda _ (fun _=> measurable_pi_apply _)))
   measurable_invFun:= by
     apply measurable_pi_lambda; intro i; cases i
     · exact measurable_pi_apply _
     rename_i i
     exact ((measurable_pi_apply _).comp L.rightMeas).comp ((key_meas L).prodMk (show Measurable (fun u:Booth L=> u ∘ Sum.inr) from measurable_pi_lambda _ (fun _=> measurable_pi_apply _))) }
 origin:= by ext1 i; cases i<;> simp only [MeasurableEquiv.coe_mk]; rfl -- simplify projection
             rename_i i; change L.dry (key L 1) (1:L.Clouds) i=_; rw [key_one,L.dry_one]; rfl
 form:= by
  intro i; cases i
  · exact neighborhood_exp _
  rename_i i
  exact crest_form L (key_form L neighborhood_exp) (extend Sum.inr (G:=G) (J:=Reference L) neighborhood_exp) (by simp [key_one]) (show expLinks G (Reference L) 0 ∘ Sum.inr=(1:L.Clouds) from by rw [identity_zero]; rfl) i
 recover:= by
  intro i; cases i
  · exact neighborhood_exp _
  rename_i i
  exact woke_form L (key_form L neighborhood_exp) (extend Sum.inr (G:=G) (J:=Reference L) neighborhood_exp) (by simp [key_one]) (show expLinks G (Reference L) 0 ∘ Sum.inr=(1:L.Clouds) from by rw [identity_zero]; rfl) i
end YM.FormalOPE.RG10.Inherit
