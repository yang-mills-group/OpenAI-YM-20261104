import YM.Contacts.Model.Shoulder
/-! Local sawtooth test avoiding differentiation of the LISTING in another volume.
 No Euclidean shell seam asserted. Entirely discrete. -/
noncomputable section
namespace YM.Contacts.Model.Slope
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{m:Side}{n k:ℕ}{p:PlaqAxes}
open Averaging (axes01)
variable (X: G.ColorIndex)
def pedal : G.Color:= EuclideanSpace.single X 1
@[simp] lemma pNorm : ‖pedal X‖=1:=by simp [pedal,EuclideanSpace.single]
variable (n) -- implicit status
abbrev bolt : Link G m := imp (Exterior.coord 1,X) fun x:Site m=> saw n (x 0)
lemma ticket (hm:m.val=2*n): ‖bolt n X (m:=m)‖≤n := by
   refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2 ?_; rintro ⟨x,i,j⟩; unfold bolt imp; split; next h=>
      have ht:= (Slide.stamp hm.ge x); have hb:=Slide.crystal_le _ ht; have he:=box_test.mp hb; let s:Cover:=Slide.stage (Slide.cognac hm.ge) x; change ‖(s 0:ℝ)‖≤ (n:ℝ); rw [Real.norm_eq_abs]; apply abs_le.mpr; exact_mod_cast (And.intro (he.1 0) (he.2 0))
   simp
-- Direction topology bridge
def drive (e:Edge (Site m)) : G.Color := if (1:Axis)=e.2 then saw n (e.1 0) • pedal X else 0
lemma wheel (x:Site m)(b:Axis): (arm G m 1 (bolt n X)) (x,Exterior.coord b)=drive n X (x,b):= by
   ext1 j; by_cases h:(1:Axis)=b
   · subst b; by_cases hz:j=X <;> simp [bolt,imp,drive,arm_apply,hz, pedal,PiLp.smul_apply,EuclideanSpace.single] -- check
   have hb: Exterior.coord b ≠ Exterior.coord 1:= (axisEquiv.injective.ne (Ne.symm h))
   simp [arm_apply,bolt,imp,drive,h,hb]  
lemma pumps {f: Config G m→ℝ}{B:BudgetPoint}{s:Lattice.Support m}(hG:G.Simple)(hf:B.Regular s f)(ha:altitude f): logHessian f (drive n X) (drive n X)=2*jet (f∘ input G m) 2 (bolt n X):= by
   erw [show logHessian _ _ _= _ from (Work.F03.line_second (germ_diff hf) (flat_critical hG hf) (drive n X)).symm, homogeneous_derivative _ _ _ (ha.contDiffAt.of_le le_top)]
   rw [← mul_assoc,show (2:ℝ) * ((Nat.factorial 2:ℝ)⁻¹)=1 by norm_num [Nat.factorial],one_mul]; apply congr_arg (iteratedDeriv 2 · 0); funext t; apply congr_arg f; funext ⟨x,b⟩; simp only [increment,Pi.smul_apply,Pi.one_apply,mul_one,encode_link,map_smul,wheel]
variable {n}
def lull (v:G.Color) : LinearJet G:= ⟨fun k=> if (1:Axis)=k then v else 0,0⟩
local notation "M" =>(drive (m:=m) n X)
def well (X:G.ColorIndex)(n:ℕ)(u:Site m):= (lull (saw n (u 0) • pedal X)).field u
abbrev Vibe (o: Site m):= M-well X n o
lemma riot (u x:Site m)(k:Axis) : Vibe X (n:=n) u (x,k)= if (1:Axis)=k then (saw n (x 0)-saw n (u 0)) • pedal X else 0:= by unfold Vibe well; simp only [lull,LinearJet.field, Pi.sub_apply, drive, sub_smul]; split <;> simp
variable (hm:m.val=2*n)
lemma lift₀ (o x:Site m) : o 0+(lift (x-o) 0:Per m)=x 0:= by rw [show ((lift (x-o) 0:ℤ):Per m)=(x-o) 0 from congr_fun (wrap_lift (x-o)) 0]; change o 0+(x 0-o 0)=x 0; abel
include hm
lemma vibe_dir (u:Site m)(B:BudgetPoint): B.dirBound u (B.threshold • Vibe X (n:=n) u) := by
   rintro ⟨x,b⟩; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg B.threshold_pos.le,riot]; apply mul_le_mul_of_nonneg_left _ B.threshold_pos.le
   let Y:=saw n (x 0); split; next h=>
      rw [norm_smul,pNorm,mul_one]; have h:=pathBound' hm (u 0) (lift (x-u) 0); rw [lift₀] at h; refine h.trans (((Nat.cast_le (α:=ℝ)).2 (component_le (x-u) 0)).trans (le_trans (show (separation x u:ℝ)≤ 1+↑(separation x u) by linarith) ?_)) -- he
      have he:= B.power_ge; simpa using pow_le_pow_right₀ (show (1:ℝ)≤1+↑(separation x u) by simp) (show 1≤B.power by omega)
   simp only [norm_zero, ge_iff_le]; positivity
lemma auspice {u:Site m}(hu:openBank n k (u 0)): Agrees (neighbors k u) (Vibe X (n:=n) u) (hand n (u 0) • (wedge axes01 (pedal X)).field u):= by
   rintro ⟨x,b⟩ hx _; rw [riot,Pi.smul_apply,wedge_field]; have he : separation x u≤k:= (separation_comm x u).trans_le ((neighbors_mem ..).1 hx); change (if (1:Axis)=_ then _ else _) = hand n _ • (if (1:Axis)=_ then _ else _); split_ifs; · rw [show saw n (x 0)- _= _ from (show saw n (x 0)- saw n (u 0)= hand n (u 0)* VerifiedReset.coord u x axes01.val.1 from (by rw [← lift₀ u x]; exact bears hm ((component_le (x-u) 0).trans he) hu)), mul_smul]
   simp
variable {f:Config G m→ℝ}{B:BudgetPoint}{o:Site m}(hG:G.Simple)(hf:B.Regular (neighbors k o) f) (hy:20< m.val) (ht:10*k< m.val)
omit hm
include hf hG ht hy
lemma wings : logHessian f (Vibe X (n:=n) o) (Vibe X (n:=n) o)=logHessian f M M:= by
  let v:=saw n (o 0) • pedal X; let e : LinearJet G:=lull 0; have he: e.field (G:=G) o=0:= by unfold e LinearJet.field lull; ext1 z; simp
  have h (u:Directions G m) : logHessian f (Vibe X (n:=n) o) u=logHessian f M u:= by
     have ha:= (lull v).hessian_curl₁ hG hf (holds k o ht) (by omega) e rfl u; rw [he,hessian_eq f 0,map_zero] at ha; unfold Vibe well; rw [hessian_eq,map_sub,sub_apply,← hessian_eq,← hessian_eq]; exact sub_eq_self.mpr (show _=0 from ha)
  rw [h _,hessian_symm hf,h]
include hm
lemma rally {b:ℝ}(hx:B.supBounds o (neighbors k o) f b): ‖logHessian f M M‖≤ b/B.threshold^2:= by
   rw [← wings X hG hf hy ht]; let v:= Vibe X (n:=n) o; let y:=B.threshold • v; have hj:=B.order_ge; have he:‖leftDerivs f [y,y] 1‖ ≤ b:= hx.2 1 (flat_ok ..) _ (by simp; omega) (by simpa using vibe_dir X hm o B)
   apply (le_div_iff₀ (sq_pos_of_pos B.threshold_pos)).2; rw [mul_comm,← Real.norm_of_nonneg (sq_nonneg B.threshold),← norm_mul,show B.threshold^2 *_= _ from (?_ :B.threshold^2 *logHessian f v v=leftDerivs f [y,y] 1)]; exact he
   rw [← hessian_diag hG hf]; unfold y; rw [hessian_eq,hessian_eq,map_smul,map_smul,smul_apply]; simp only [smul_eq_mul]; ring
lemma shine (hv:openBank n k (o 0)): logHessian f M M = coeff f o axes01 axes01:= by
   rw [← wings X hG hf hy ht,hessian_agrees hG hf (auspice X hm hv) (auspice X hm hv),hessian_eq,map_smul,map_smul,smul_apply]; simp only [smul_eq_mul]; rw [← mul_assoc,(sign_price _).1,one_mul,← hessian_eq,label_color o hG hf,real_inner_self_eq_norm_sq,pNorm,one_pow,mul_one]
end YM.Contacts.Model.Slope
