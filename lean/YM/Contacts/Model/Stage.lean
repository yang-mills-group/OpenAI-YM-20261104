import YM.Contacts.Model.Seat
/-! Exact accounting of stationary rays across Slide. Used uniformly (height Δ paid elsewhere).
     No cost assumptions on models; tiles don't need to be small for identity of rays.
 -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c C:Side}{k w r z:ℕ}

section wedge
variable (A:Slide.Track n)(u:Site m)
def denial : Link G m →L[ℝ] Link G n := ContinuousLinearMap.pi fun i:Lines G n 1 =>
  let x:=i.1; let p:=Exterior.axisEquiv.symm i.2.1; let y:=Slide.sites A u
  if Slide.grade A (x,p)=1 then ContinuousLinearMap.proj (y x,i.2) else if Slide.grade A (x,p)=-1 then -(ContinuousLinearMap.proj (y (x+step p),i.2)) else 0
lemma den (x:Site n)(i:Axis)(v:Link G m): arm G n 1 (denial A u v) (x,coord i)= if Slide.grade A (x,i)=1 then arm G m 1 v (Slide.sites A u x,coord i) else if Slide.grade A (x,i)= -1 then -arm G m 1 v (Slide.sites A u (x+step i),coord i) else 0:= by
   ext1 j; split
   next h=> simp only [arm_apply, denial,ContinuousLinearMap.pi_apply, show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i,h]; rw [if_true]; rfl
   next hh=> split
             next h=> simp only [arm_apply,denial,ContinuousLinearMap.pi_apply, show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i,if_neg hh,if_pos h]; rfl
             next h=> simp only [arm_apply,denial,ContinuousLinearMap.pi_apply, show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i,if_neg hh,if_neg h]; rfl
lemma okn (v:Link G m) : Slide.shape A u (input G m v)= input G n (denial A u v):= by
   ext1 ⟨x,b⟩; rw [encode_link, den]; unfold Slide.shape; dsimp only; split; next h=> exact encode_link ..
   next hh=> split; next h=> rw [encode_link]; exact (Work.F03.exp_neg_color _).symm
             next h=> simp
lemma nor_den : ‖denial (G:=G) A u‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=>by
   rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2; rintro ⟨x,i,k⟩; unfold denial; rw [ContinuousLinearMap.pi_apply]; dsimp only; split; · exact le_trans (le_of_eq (by simp)) (norm_le_pi_norm y (Slide.sites A u x,i,k))
   split; · simp only [_root_.neg_apply,ContinuousLinearMap.proj_apply,norm_neg]; exact norm_le_pi_norm y _
   simp)
lemma nor_turn (s:Signed) : ‖orderTurn (G:=G) (m:=m) s‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=>by
   rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2; rintro ⟨x,i,k⟩; obtain ⟨i,rfl⟩:= axisEquiv.surjective i; erw [flip_price]; split_ifs; rw [norm_neg]; exact norm_le_pi_norm _ _; exact norm_le_pi_norm _ _)
abbrev plays (F:Offer G n):= froth F ∘ input G n
-- comp capture derivatives
abbrev altitude (f: Config G n→ℝ) := AnalyticAt ℝ (f ∘ input G n) 0
lemma shape_ana {f:Config G n→ℝ}(h:altitude f): altitude (f ∘ Slide.shape A u) := by
   rw [Model.altitude, show ((f ∘ Slide.shape A u) ∘ input G m)=(f ∘ input G n)∘ denial A u from funext fun i=>congr_arg _ (okn A u i)]
   exact Forge.starts _ h _
lemma citizen_hue (F:Story G)(x:Site c)(V:Config G c) : pass (hue F) c x V= VerifiedReset.factor * ∑ i:Signed, pass F c (i⁻¹.act x) (pull i 0 V):= by
   unfold pass hue; refine congr_arg _ (sum_congr rfl fun i _=>?_); rw [expandAt_pull,affine,add_zero,Signed.act_inv]
variable {D: Stars→Side}(Q:∀ i:Stars,(D i).val=2*(w+i.val)) (Y:∀ i:Stars,Config G (D i)→ℝ) (ht:∀ i,altitude (Y i))
lemma fitted_at (F:Story G)(i:Signed)(x:Site c)(p:Link G c): pass F c x (pull i 0 (input G c p))= pass F c x (input G c (orderTurn i p)):= congr_arg _ (flip_links ..)
lemma adapted_hue {F:Story G}(h: ∀ x:Site n,altitude (pass F n x))(x:Site n): altitude (pass (hue F) n x) := by
   unfold altitude Function.comp; simp_rw [citizen_hue,fitted_at]; apply ContDiffAt.analyticAt; exact contDiffAt_const.mul (ContDiffAt.sum (fun i _=> (Forge.starts _ (h (i⁻¹.act x)) (orderTurn i)).contDiffAt))
lemma froth_apt {F:Offer G n}(h:∀ x:Site n,altitude (F x)) : altitude (froth F) := by unfold froth altitude Function.comp; exact ContDiffAt.analyticAt (ContDiffAt.sum fun _ _=> (h _).contDiffAt)
include ht
lemma modulates (x:Site c): altitude (pass (Model.clock Q Y) c x) := by
   exact ContDiffAt.analyticAt (ContDiffAt.sum (f:=fun i p=> Slide.ray i*Y i (shape (Trio.pad Q i) (expandAt x (input G c p)))) (x:=(0:Link G c)) (s:=univ) (fun i _=> contDiffAt_const.mul (shape_ana (Trio.pad Q i) x (ht i)).contDiffAt))
lemma adopts (x:Link G c)(r:ℕ): Radial.jet (plays (pass (Model.clock Q Y) c)) r x =∑ p:Site c, ∑ i:Stars,Slide.ray i* Radial.jet (Y i ∘ input G (D i)) r (denial (Trio.pad Q i) p x) := by
   rw [show plays _= _ from (show plays (pass (Model.clock Q Y) c) = (fun x=>∑ p:Site c,pass (Model.clock Q Y) c p (input G c x)) from rfl)]; erw [loan_sum _ fun i _=> modulates Q Y ht i]; apply sum_congr rfl; intro p _
   let F (i:Stars):=Y i∘ input G (D i); let g (i:Stars) := F i ∘ denial (Trio.pad Q i) p; have hv i: AnalyticAt ℝ (g i) 0:= Forge.starts _ (ht i) _
   erw [show pass (Model.clock Q Y) c p ∘ input G c=(fun v=>∑ i:Stars, Slide.ray i*g i v) from (by ext x; unfold pass Model.clock; dsimp only [Function.comp]; exact sum_congr rfl (fun i _=>congr_arg (fun v:Config G (D i)=> Slide.ray i*Y i v) (okn (Trio.pad Q i) p x))), loan_sum _ fun i _=> analyticAt_const.mul (hv i)]; apply sum_congr rfl; intro i _; rw [← show Radial.jet (g i) r x= _ from (Garf.woven (F:=F i) (ht i) _ _ _)]; unfold Radial.jet; erw [show (fun x:Link G c=> Slide.ray i)*g i =Slide.ray i • g i from rfl,iteratedFDeriv_const_smul_apply (hv i|>.contDiffAt)]; change _* (Slide.ray i*_) = _; ring_nf; try rfl
omit ht
lemma breeze {F:Story G}(h:∀ p:Site c, altitude (pass F c p))(x:Link G c)(r:ℕ): Radial.jet (plays (pass (hue F) c)) r x=VerifiedReset.factor *∑ i:Signed,Radial.jet (plays (pass F c)) r (orderTurn i x):= by
   let f (i:Signed):=(plays (pass F c)) ∘ (orderTurn (G:=G) i); have hx i:AnalyticAt ℝ (f i) 0:= Forge.starts _ (froth_apt h) _
   rw [show plays (pass (hue F) c) = VerifiedReset.factor • (fun x=>∑ i:Signed,f i x) from (by funext x; change froth (pass (hue F) c) (input G c x)= _; rw [from_home F]; apply congr_arg; exact sum_congr rfl (fun i _=>congr_arg _ (flip_links ..)))]
   have hv: AnalyticAt ℝ (fun x=>∑ i:Signed,f i x) 0:= ContDiffAt.analyticAt (ContDiffAt.sum (fun i _=> (hx i).contDiffAt)); rw [show Radial.jet (VerifiedReset.factor • _) r x= VerifiedReset.factor * Radial.jet (fun x=>∑ i:Signed,f i x) r x from ?_, loan_sum _ fun i _=> hx i]; exact congr_arg _ (sum_congr rfl fun i _=> Garf.woven (froth_apt h) _ _ _); unfold Radial.jet; erw [iteratedFDeriv_const_smul_apply hv.contDiffAt]; change _*(VerifiedReset.factor* _) = _; ring_nf; try rfl
end wedge
end YM.Contacts.Model
