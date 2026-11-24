import YM.Contacts.Model.Heir
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
open Slope
-- template kinetics on Cover (no flags).
def flange (G:Gauge)(a:ℝ): Story G:= fun U=> ∑ i:PlaqAxes,(a/2)*inner ℝ (StressFlux.clover U 0 i.val.1 i.val.2) (StressFlux.clover U 0 i.val.1 i.val.2)
open StressFlux (clover sign plate)
def padM (a : ℝ) (i j : PlaqAxes) : ℝ:= if i=j then a else 0
variable (x:Site m)(a:ℝ) {f:Story G}
open CouplingShape (parityPrice)
lemma forms : pass (flange G a) m x=VerifiedReset.counter (padM a) x := by
   ext U; unfold VerifiedReset.counter pass flange VerifiedReset.quad padM petals; have he i j : clover (expandAt x U) 0 i j= clover U x i j := by
      have ht p q: plate (expandAt x U) 0 p q= plate U x p q:= by unfold plate; rw [travel_at,map_zero,zero_add]
      simp_rw [clover,StressFlux.stencil, ht]
   simp_rw [he,ite_mul,zero_mul]; simp only [sum_ite_eq,Finset.mem_univ,if_true,sum_div]; apply sum_congr rfl; intro i _; ring
variable {x}
lemma flange_power (r:ℝ) : flange G (r*a)=r • flange G a:= by funext i; simp only [flange, Pi.smul_apply,smul_eq_mul,mul_sum]; apply sum_congr rfl; intro j _; ring
lemma flange_spin : Adapted (flange G a):= by
   intro s U; unfold flange; refine Finset.sum_equiv (PlaqAxes.transform s) (by simp) (fun p _=> ?_); apply congr_arg
   let x:=p.val.1; let y:=p.val.2; let k:=PlaqAxes.rotate s p; let u:= parityPrice s p -- namespace
   have hh:clover (pull s 0 U) 0 x y=u • clover U (affine s 0 0) k.val.1 k.val.2:= by
     unfold u parityPrice k; rw [StressFlux.clover_pull]; unfold PlaqAxes.rotate PlaqAxes.ordered
     rcases lt_or_gt_of_ne (show s.perm x≠s.perm y from s.perm.injective.ne p.property.ne) with hh|hh
     · simp only [min_eq_left hh.le,max_eq_right hh.le,hh, if_true,mul_one, x,y]
     rw [StressFlux.clover_swap U _ (s.perm x)]; simp [min_eq_right hh.le, max_eq_left hh.le, if_neg (not_lt.mpr hh.le) , x,y]
   erw [hh,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_smul]; simp only [u,Real.norm_eq_abs,CouplingShape.parityPrice_abs,one_mul,affine]; simp; rfl
lemma flange_local (hz:4≤z) : LocalOn (Lattice.box z) (flange G a):= by
   intro U V he; have ht p q: plate U 0 p q= plate V 0 p q:= by
      apply congr_arg G.curvature; apply travel_local; intro i h h'
      let Q:= Lattice.oriented p q; have hh (i: Cover)(h:i∈ visits 0 Q): i∈Lattice.box z:= by apply scene_lt; apply (fees_step _ (0:Cover) h).trans; simp [Laurent.size,hz,Q,Lattice.oriented]
      exact he i (hh _ h) (hh _ h')
   simp only [flange,clover, StressFlux.stencil, ht]
section support
variable (B:BudgetPoint)
lemma face_bill (hz:2≤z) : B.Regular (neighbors z x) (pass (flange G a) m x):= by rw [forms (G:=G)]; refine reg_larger (counter_regular ..) ?_ ; rw [←plus_no z x hz]; exact Finset.subset_union_right
lemma face_price (G:Gauge)(_hz:2≤z) : B.supBounds x (neighbors z x) (pass (flange G a) m x) (|a| *((2:ℝ)⁻¹*(Fintype.card PlaqAxes:ℝ)*(pairBill G B*B.threshold^2))):= by
   rw [forms]; let v:= ∑ i:PlaqAxes,∑ j:PlaqAxes, |padM a i j| *(pairBill G B*B.threshold^2); apply sup_le ((counter_bill x _ B).sup fun _ hv => healthy_mono (singleton_subset_iff.mpr (addr z x).anchor) hv); unfold padM; simp_rw [apply_ite abs,abs_zero,ite_mul,zero_mul]; simp only [sum_ite_eq,Finset.mem_univ,if_true,sum_const,nsmul_eq_mul,card_univ]; exact le_of_eq (by ring)
lemma rescinded {f:Story G}{C:ℝ} (hG:G.Simple)(h:C=deposit (pass f m))(he:∀ v,B.Regular (neighbors z v) (pass f m v))(hk:Adapted f)(hz:2≤z)(ht:10*z< m.val) : let v:=pass (f-flange G C) m x; ∀ i j,IsAffineDirection x i→IsAffineDirection x j→logHessian v i j=0:= by
   intro v; have hh:padM C=VerifiedReset.projection (addr z x) (pass f m x):= funext fun i=> funext fun j=> by rw [padM,h,holder hG he hz ht (reflects f hk)]
   rw [show v= (pass f m x) - VerifiedReset.counter (VerifiedReset.projection (addr z x) (pass f m x)) x from (by rw [← hh,← forms]; rfl)]
   let w o:= pass f m o; let p':= padM C; let a':= addr z x; rw [← hh]; have ha:B.Regular (neighbors z x) (VerifiedReset.counter p' x (G:=G)):= by rw [show VerifiedReset.counter p' x (G:=G)=pass (flange G C) m x from (forms x C).symm]; exact face_bill C B hz
   apply affine_zero (reg_sub (he x) ha); intro i; rw [hessian_sub (he x) ha, counter_diag hG B x (by omega) i,show p'=padM C from rfl,hh,projection_eq (a:=addr z x) (f:=pass f m x) hG (he x) (by rw [plus_no z x hz]; exact holds z x ht),show (addr z x).site=x from rfl,sub_eq_zero]; exact LinearJet.hessian_curl hG (he x) (holds z x ht) (by omega) (positive_primitive ..).symm (positive_primitive ..).symm
end support
section rents
variable {E Z:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {U:E→ Config G n}{y:E}{v b:ℝ}
  (h:∀ i,Allows k (fun x=>G.mat (U x i)) y v)
open Next.Scheduling
-- derivative gross envelope. Paid after ratios.
def stemCost (G:Gauge)(v:ℝ)(k:ℕ) := 
    let normL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
    normL (Wages.projector G)* travelCost G k 4 v
def returnCost (G:Gauge)(v a:ℝ)(k:ℕ) := (Fintype.card PlaqAxes:ℝ)*(|a/2| * (2^k*(stemCost G v k)^2))
lemma votes' [NormedAddCommGroup Z][NormedSpace ℝ Z]{f g:E→Z}(hf:Allows k f y b)(hg:Allows k g y v): Allows k (fun x=>f x-g x) y (b+v):= by
   have hh:=hf.add (hg.smul (-1)); norm_num [sub_eq_add_neg] at hh ⊢; exact hh
include h
lemma cloverly (o:Site n): Allows k (pass (flange G a) n o ∘ U) y (returnCost G v a k):= by
   let T:= stemCost G v k; have he i j : Allows k (fun z=>plate (U z) o i j) y T:= (travel_jets h o (show List.length (Lattice.oriented i j)≤4 from le_rfl)).linear (Wages.projector G) le_rfl
   have hh i j : Allows k (fun z=> clover (U z) o i j) y T:= by
      apply (((votes' (votes' (he _ _) (he _ _)) (votes' (he _ _) (he _ _)))).smul (4:ℝ)⁻¹).mono ?_; norm_num; linarith
   rw [forms]; let P (i:PlaqAxes) (x:E):=petals (U x) o i; let f (i:PlaqAxes) x:= (a/2)*inner ℝ (P i x) (P i x)
   have hx i: Allows k (f i) y (|a/2| *((2:ℝ)^k*T^2)):= (((Allows.bilinear (innerSL ℝ) (hh _ _) (hh _ _) (norm_innerSL_le ℝ)).smul (a/2))).mono (by ring_nf; rfl) -- arguments implicit
   apply Allows.germ ((allows_sum (s:=univ) fun i _=> hx i).mono ?_); swap; · unfold returnCost T; rw [sum_const,nsmul_eq_mul,card_univ]
   exact Eventually.of_forall (fun i=> by unfold VerifiedReset.counter VerifiedReset.quad padM; simp only [Function.comp_apply]; rw [sum_div]; apply Finset.sum_congr rfl; intro j _; simp only [ite_mul,zero_mul,sum_ite_eq,Finset.mem_univ,if_true]; unfold f P; ring)
end rents
end YM.Contacts.Model
