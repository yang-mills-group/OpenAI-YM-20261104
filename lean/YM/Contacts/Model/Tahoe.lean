import YM.Contacts.Model.Arbor
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
namespace Arbor
open Lintel.Plata ConnectedActivityE6 Next.Fluctuations
variable {Υ C A Λ H t R D I O Z μ:ℝ}{v:ℕ}{S:ℝ≥0}{X:G.ColorIndex}{P:Bed}
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{U:E → Config G m}{u:E}
variable (hy: Inputs U k Z)
lemma send_comp (s:Signed)(hA:∀ i, Allows k (fun x=>G.mat (U x i)) u Z) (i:Bond m): Allows k (fun x=> G.mat (pull s 0 (U x) i)) u Z:= by
   unfold pull Lattice.Step.read; split; next _=> exact (hA _).inverse -- measure
   exact hA _
omit hy
lemma send_pay (s:Signed)(h:Inputs U k Z): Inputs (pull s 0 ∘ U) k Z := ⟨by rw [Function.comp_apply,h.1]; exact pull_one_field .., h.2.1,fun i x hx => send_comp s (fun i=> h.2.2 i x hx) i⟩
variable {p:Clip}(T:PathData G)(F:bore G)(h:Aegis X F P)(hG:G.Simple)(hP:Tills (z+3) S C F)(hp:m.val≤v)(he:i<z+3)
-- v bound m. price polynomial.
lemma enoughChart (h:PaintSupply G k Z) : Inputs (input G m) k (outerCost G k Z):= by
   have he i j (hj:‖j‖≤1) := imprints (n:=m) h (x:=j) hj i; exact ⟨by simp,(he (Classical.arbitrary _) (0:Link G m) (by simp) |>.nonneg), fun i j hj=> he i j hj⟩ -- metavars arbitrary
include hy h hG hP hp he
def sufficient (G: Gauge) (v:ℕ) (Z d:ℝ) := (2*(4*(v:ℝ))+1) * (Inputs.variation G Z * d) < Kale.charHeight G
def tollP (G:Gauge)(p:Clip)(v z k:ℕ)(C Z μ I Λ:ℝ):= arcPrice G v k z Z C + (v:ℝ)^4*sumFee G p Z μ I Λ k
lemma atEase (hQ:T.Bounds p μ I Λ)(d:ℝ)(hd:d<1) (hh:sufficient G v Z d)(hz:‖u‖≤d)(hu:1≤k): Allows k (anchor p T F m (z+3) i ∘ U) u (tollP G p v (z+3) k C Z μ I Λ):= by
   have hw: u∈ ball (0:E) 1:= mem_ball_zero_iff.mpr (hz.trans_lt hd); have hw': ‖u‖≤1:= hz.trans hd.le
   have ht : Allows k (Kale.mirror (Kale.fire (wind (hair F m) (z+3) i)) ∘ U) u (arcPrice G v k (z+3) Z C):= by
     apply allows_average (f:=fun (s:Signed) y=> Kale.fire (wind (hair F m) (z+3) i) (pull s 0 (U y))); intro s; let w:= send_pay s hy; have hx i:G.chord (pull s 0 (U u) i) ≤ Inputs.variation G Z * d:= (w.chord hu hw' i).trans (mul_le_mul_of_nonneg_left hz (div_nonneg hy.2.1 G.colorScale_pos.le)); exact vizPrice F h hG hP hp he (fun i=> w.2.2 i u hw') hx hh
   let V:=sumFee G p Z μ I Λ k; have hh': Allows k (base p T m i ∘ U) u ((Fintype.card (Site m):ℝ)*V):= by
      rw [← uses]; exact Model.train _ (fun i'=>outerBrush p T isOpen_ball (convex_ball _ _).isPreconnected hw (fun i u hu=>hy.2.2 i u (mem_ball_zero_iff.mp hu).le) _ i' hQ i) -- p Binder? print
   refine ((votes' ht hh')).mono ?_; apply add_le_add_right; refine mul_le_mul_of_nonneg_right ?_ (sumFee_nn p); simp [Site,Per,Four,Axis]; gcongr
omit hy h hG hP hp he
-- Taylor on balls.NB no positive threshold for k. Rank 0.
open Blaze
section rebate
variable {d:ℝ}[FiniteDimensional ℝ E]{f:E→ℝ}
variable (hK:∀ x, x∈ closedBall (0:E) d→ Allows k f x C) (hyZ:∀ x:E,∀ i<j,jet f i x=0)
include hK hyZ
lemma sap {z:ℕ} (hu: j≤ k)(h:z ≤ j)(hx:u∈closedBall (0:E) d): normJ z f u ≤ C*d^(j-z):= by
   have ht:0≤d:= (norm_nonneg _).trans (mem_closedBall_zero_iff.mp hx); have he: (0:E)∈closedBall (0:E) d:= mem_closedBall_self ht
   induction h using Nat.decreasingInduction generalizing u with
   | self=> simpa only [Nat.sub_self,pow_zero,mul_one] using (hK u hx).norm_le j hu
   | of_succ y hyZ' ih=>
      let X:= closedBall (0:E) d; let b:=iteratedFDeriv ℝ y f; let t:=C*d^(j-(y+1)); have hT:0≤t:= mul_nonneg (hK 0 he|>.nonneg) (pow_nonneg ht _)
      have ha:b 0=0:= (rays_jet ((hK 0 he).analytic.analyticAt) j).1 ((jet_bridge ((hK 0 he).analytic.analyticAt)).2 hyZ) y hyZ'
      have hz (u) (hx:u∈X) : DifferentiableAt ℝ b u:= (hK u hx).analytic.differentiableAt_iteratedFDeriv (by simp)
      have hZ (w)(hw:w∈X): ‖fderiv ℝ b w‖≤ t:= norm_fderiv_iteratedFDeriv.trans_le (ih hw) -- order
      have he: ‖b u‖ ≤ t*‖u‖:= by simpa only [ha,sub_zero] using Convex.norm_image_sub_le_of_norm_fderiv_le hz hZ (convex_closedBall _ _) he hx -- API
      apply he.trans ((mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hT).trans_eq ?_); unfold t; rw [mul_assoc,← pow_succ,show j-(y+1)+1=j-y from by omega]
lemma potCap (h : j ≤ k)(hv:0<d)(ht:d≤1)(hx:u∈closedBall (0:E) d): Brush k (C*d^j) d⁻¹ f u:= by
   have hu:=hK u hx; refine ⟨hu.analytic.of_le le_top,inv_nonneg.mpr hv.le, fun z hR=>?_⟩; rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hv z)]; by_cases hz:z ≤ j; · refine le_trans (mul_le_mul_of_nonneg_right (sap hK hyZ h hz hx) (pow_pos hv z).le) (le_of_eq ?_); rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hz]
   refine le_trans (mul_le_mul_of_nonneg_right (hu.norm_le _ hR) (pow_pos hv z).le) (mul_le_mul_of_nonneg_left ?_ hu.nonneg); exact pow_le_pow_of_le_one hv.le ht (by omega)
end rebate
-- CTO expenses even for huge n when via Slide seams. use super height.Actual
lemma inputs_trap (T:Slide.Track c) (h : Inputs U k Z) (o:Site m) : Inputs (Slide.shape T o ∘ U) k Z:= by
   refine ⟨?_,h.2.1,?_⟩; · rw [Function.comp_apply,h.1]; funext i; unfold Slide.shape; split; rfl; split; simp; rfl
   intro i x hx; unfold Function.comp Slide.shape; have hh i:= h.2.2 i x hx; split; exact hh _; split; exact (hh _).inverse; apply allows_const; exact (show ‖G.mat 1‖≤Z from by let v:Bond m:= Classical.arbitrary _; have he:= (h.2.2 v 0 (by simp)).value; rw [h.1] at he; exact he) -- syntax
include h hG hP he hy
def upCard (G:Gauge)(p:Clip)(v z k:ℕ)(C Z μ I Λ:ℝ):= ∑ i:Stars, |Slide.ray i| * tollP G p v z k C Z μ I Λ
variable {Y:Stars→Side}(Q:∀ i:Stars,(Y i).val=2*(ℓ+i.val)) (hh':∀ i,(Y i).val≤v)
include hh'
lemma upfront (hQ:T.Bounds p μ I Λ)(d:ℝ)(hd:d<1) (hh:sufficient G v Z d)(hz:‖u‖≤d)(hu:1≤k) (o: Site m): Allows k (pass (energy p T F Q (z+3) i) m o ∘ U) u (upCard G p v (z+3) k C Z μ I Λ):= by
    unfold energy Function.comp; simp_rw [citizen_hue]; apply allows_average (f:=fun s y=> pass (Model.clock Q _) m (s⁻¹.act o) (pull s (0:Site m) (U y))); intro s; let a:=s⁻¹.act o
    have hx : Inputs (pull s 0 ∘ U) k Z:= send_pay s hy; unfold pass Model.clock; refine allows_sum (f:=fun t x=> _ * anchor p T F (Y t) (z+3) i (Model.shape (Trio.pad Q t) (expandAt a (pull s 0 (U x))))) ?_; intro i₂ _; exact (atEase (inputs_trap (Trio.pad Q i₂) hx a) T F h hG hP (hh' i₂) he hQ d hd hh hz hu).smul _
omit h hG hP he hy hh'
lemma arborTicket_nat (z:ℕ): 1 ≤ z+1:=by omega
open Boulevard (actual)
def settle (c:Side) : Positions (Push.Uniform.Primary c G) →L[ℝ] Link G c:= ContinuousLinearMap.pi fun i:Lines G c 1=> ContinuousLinearMap.proj ((i.1,i.2.1),i.2.2)
lemma borne (v:Positions (Push.Uniform.Primary m G)): input G m (settle m v)=actual v:= by exact rfl
lemma due (m:Side): ‖settle (G:=G) m‖≤1:= by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v=> norm_le_pi_norm x _
def holdOn (k:ℕ)(Z:ℝ):= composeCost k Z 1
lemma canyon (hP:PaintSupply G k Z) (m:Side): Inputs (actual («G»:=G) (c:=m)) k (holdOn k (outerCost G k Z)):= by
    rw [show actual («G»:=G) (c:=m)=input G m ∘ settle m from funext fun i=> (borne _).symm]; let L:=settle (G:=G) m; have h:‖L‖≤1 := due _; have hp:=enoughChart (m:=m) hP; have hv (x:Positions (Push.Uniform.Primary m G))(hx:‖x‖≤1): ‖L x‖≤1:= L.le_of_opNorm_le h x|>.trans ((one_mul ‖x‖).trans_le hx);
    have hZ x (hx:‖x‖≤1) i : Allows k (fun y=> G.mat (input G m (L y) i)) x (holdOn k (outerCost G k Z)):= ((hp.2.2 i (L x) (hv x hx)).comp (f:=⇑L) (allows_linear h (hv x hx))); exact ⟨by simp [hp.1], (hZ 0 (by simp) (Classical.arbitrary _)).nonneg,fun i x hx=> hZ x hx i⟩
end Arbor
end YM.Contacts.Model
