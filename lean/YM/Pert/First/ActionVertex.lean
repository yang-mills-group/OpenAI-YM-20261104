import YM.Pert.First.CubicPrice
/-! Local stencils and the summed order-one action vertex, including the inversion multiplicity, directly from the same `Orb.action`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Pert.First
open Lattice Filter Function Orb Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {N : Side} {X : Type*} [AddCommGroup X] [One X]
/-- Uniform notation for links at a single oriented face (organized in multiplication order). -/
def Vleft (x : Four X) (i : Axis) (v : Links X G.Color) := v (x,i)
def Xleft (x : Four X) (i j : Axis) (v : Links X G.Color) := v (x+step i,j)
def Vright (x : Four X) (i j : Axis) (v : Links X G.Color) := -v (x+step j,i)
def Xright (x : Four X) (j : Axis) (v : Links X G.Color) := -v (x,j)
def curlAt (x : Four X) (i j : Axis) (v : Links X G.Color) := linearSq (Vleft x i v) (Xleft x i j v) (Vright x i j v) (Xright x j v)
def bracketAt (x : Four X) (i j : Axis) (v : Links X G.Color) := bracketSq (Vleft x i v) (Xleft x i j v) (Vright x i j v) (Xright x j v)
lemma curlAt_eq (x : Site N) (v : Links (Per N) G.Color) (i j) : curlAt x i j v = cur v x i j := by unfold curlAt linearSq cur Vleft Xleft Vright Xright; abel
-- inversion of transport just negates the input log direction (matrix equality at every real t)
theorem glow_inv (v : G.Color) (t : ℝ) : G.mat ((G.lieExp (t • v))⁻¹) = glow (-v) t := by rw [glow, smul_neg, ←Work.F03.exp_neg_color]
lemma plaq_path (x : Site N) (i j) (v : Potential G N) : (fun t:ℝ=> G.mat (plaquette (t • v) x i j)) = square_path (Vleft x i v.val) (Xleft x i j v.val) (Vright x i j v.val) (Xright x j v.val) := by funext t; simp only [plaquette,map_mul,positiveLinks,G.mat_mul,SetLike.val_smul,Pi.smul_apply]; unfold square_path Vleft Xleft Vright Xright; rw [glow_inv,glow_inv]; rfl
lemma plate_tried (x : Site N) (i j) (v : Potential G N) :
    Tried (G.mat ∘ (fun t:ℝ=> plaquette (t • v) x i j)) (cur v.val x i j) (bracketAt x i j v.val) := by rw [←curlAt_eq,show G.mat ∘ _=_ from plaq_path ..]; exact square_tried
lemma lineJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Potential G N→ E) (k) (u) (hf : ContDiff ℝ ∞ f) : scaleJet f k u = (k.factorial:ℝ)⁻¹ • iteratedDeriv k (fun t:ℝ=> f (t • expand G N u)) 0 := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight (expand G N u)
  unfold scaleJet; apply congrArg (fun x => (k.factorial:ℝ)⁻¹ • x)
  have e : (fun t : ℝ=> f (t • _)) = (f ∘ (L : ℝ→Potential G N)) := rfl
  rw [iteratedDeriv_eq_iteratedFDeriv,e, L.iteratedFDeriv_comp_right hf 0, L.map_zero]
  simp [L]
  exacts [WithTop.coe_le_coe.mpr le_top]
attribute [local instance] Gauge.frobInner
lemma price_smooth (i j) (x : Site N) : ContDiff ℝ ∞ (fun a : Potential G N=> G.price (plaquette a x i j)) := by simp_rw [equal_penalty]; exact contDiff_const.mul (((pos_sqDiff x i j).of_le le_top).sub contDiff_const |>.inner ℝ ((pos_sqDiff x i j).of_le le_top |>.sub contDiff_const))
lemma fixing_diff : ContDiff ℝ ∞ (fixing (G:=G) (n:=N)) := (ContDiff.sum (fun x _ => (contDiff_norm_sq ℝ).comp (takeDiv x).toContinuousLinearMap.contDiff)).div_const _
lemma aggregate_smooth : ContDiff ℝ ∞ (action G N) := by
  exact ContDiff.add ((ContDiff.sum (fun x _ => ContDiff.sum (fun i _=>ContDiff.sum (fun j _=>
    show ContDiff ℝ ∞ (fun a : Potential G N => if i<j then G.price (plaquette a x i j) else 0) by
      by_cases hj : i<j <;> simp [hj]
      · apply price_smooth
      exact contDiff_const)))).div_const _) fixing_diff
lemma fixing_scale (v : Potential G N) (t : ℝ) : fixing (t • v)=t^2*fixing v := by simp [fixing, norm_smul,Real.norm_eq_abs,sq_abs, mul_pow, Finset.mul_sum,mul_div_assoc]; rw [←Finset.mul_sum, mul_div_assoc]
lemma fixing_third (v : Potential G N) : iteratedDeriv 3 (fun t:ℝ=> fixing (t•v)) 0=0 := by simp_rw [fixing_scale]; rw [iteratedDeriv_mul_const_field]; simp [iteratedDeriv_pow]
def costVertex (x : Four X) (i j : Axis) (A : Links X G.Color) := if i<j then inner ℝ (curlAt x i j A) (bracketAt x i j A) else 0
def price_at (x : Site N) (i j : Axis) (v : Potential G N) := if i<j then G.price (plaquette v x i j) else 0
lemma mask_third (x : Site N) (i j : Axis) (v : Potential G N) : iteratedDeriv 3 (fun t:ℝ=> price_at x i j (t•v)) 0=3* costVertex x i j v.val := by
  unfold price_at costVertex; by_cases hj:i<j <;> simp only [hj, ↓reduceIte]
  · have H:= (plate_tried x i j v).square3 ((pos_sqDiff x i j |>.comp (g:=fun p : Potential G N => G.mat (plaquette p x i j)) (f:=fun t:ℝ=>t•v) (contDiff_id.smul contDiff_const)).of_le le_top)
    change iteratedDeriv 3 (fun t:ℝ=>G.price (plaquette _ x i j)) 0/6=inner ℝ _ _/2 at H
    rw [curlAt_eq]; linarith
  simp [iteratedDeriv_const]
/-- The first-order bare-action stencil in Wilson normalization. -/
def vertexW (v : Coords G N) := (-1/4:ℝ) * ∑ x : Site N, ∑ i, ∑ j, costVertex x i j (expand G N v).val
lemma total_vertex (v : Coords G N) : cubic v=(vertexW v:ℂ) := by
  let L : ℝ→L[ℝ] Potential G N := ((ContinuousLinearMap.id ℝ ℝ).smulRight (expand G N v))
  have he := show cubic v = -(↑(iteratedDeriv 3 ((action G N) ∘ L) 0):ℂ)/6 from by rw [cubic,lineJet _ _ _ aggregate_smooth,smul_eq_mul]; norm_num [L,Nat.factorial,comp_def]; ring
  have hx : action G N ∘ L = (fun t => (∑ x : Site N, ∑ i : Axis, ∑ j : Axis, price_at x i j (L t))* (2:ℝ)⁻¹) + fun t=>fixing (L t) := by funext; change ((∑ _:Site N, _)/2 + _ : ℝ)=_; simp [action,wilson,price_at,Pi.add_apply,comp_def,div_eq_mul_inv]
  have hs (x i j) : ContDiff ℝ ∞ (fun t=>price_at x i j (L t)) := by
    unfold price_at; split
    · exact ContDiff.comp (g:=fun v=>G.price (plaquette v x i j)) (f:=fun t : ℝ=> L t) (price_smooth i j x) L.contDiff
    exact contDiff_const
  have hi x i : ContDiff ℝ ∞ (fun t=>∑ j:Axis,price_at x i j (L t)) := ContDiff.sum (fun j _=>hs x i j)
  have ht x : ContDiff ℝ ∞ (fun t=>∑ i:Axis,∑ j:Axis,price_at x i j (L t)) := ContDiff.sum (fun i _=>hi x i)
  have hwa : ContDiff ℝ ∞ (fun t=>(∑ x:Site N,∑ i:Axis, ∑ j:Axis,price_at x i j (L t))* (2:ℝ)⁻¹) := ContDiff.mul (ContDiff.sum (fun x _=>ht x)) contDiff_const
  have hwb : ContDiff ℝ ∞ (fun t=> fixing (L t)) := (fixing_diff).comp (f:=L) L.contDiff
  have hq x : iteratedDeriv 3 (fun t=>∑ i:Axis,∑ j:Axis,price_at x i j (L t)) 0 = 3*(∑ i:Axis, ∑ j:Axis, costVertex x i j (expand G N v).val) := by
    simp_rw [Finset.mul_sum]
    rw [iteratedDeriv_fun_sum fun i _=> (hi x i).contDiffAt.of_le (by decide)]
    apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_fun_sum fun j _=> (hs x i j).contDiffAt.of_le (by decide)]
    exact Finset.sum_congr rfl (fun j _=> mask_third ..)
  rw [he,hx,iteratedDeriv_add,iteratedDeriv_mul_const_field]
  erw [show iteratedDeriv 3 (fun t:ℝ=>fixing (L t)) 0=0 from fixing_third _]
  rw [iteratedDeriv_fun_sum (fun x _ => (ht x).contDiffAt.of_le (by decide))]; unfold vertexW
  rw [show (∑ x : Site N, iteratedDeriv _ _ _) = (3:ℝ) * _ from (Finset.sum_congr rfl fun x _ => hq x).trans (Finset.mul_sum ..).symm]
  simp; ring
  all_goals first | exact hwa.contDiffAt.of_le (by decide) | exact hwb.contDiffAt.of_le (by decide)
lemma curvature_second_on (x : Site N) (i j : Axis) (v : Potential G N) : iteratedDeriv 2 (fun t:ℝ => Bare.plate x [] i j (t • v)) 0 = bracketAt x i j v.val := by
  have ht (a : Potential G N) : Bare.plate x [] i j a = (recoverL G) (G.mat (plaquette a x i j)) := by unfold Bare.plate Bare.plateU; simp [Bare.square_links,travel,stop, plaquette,recover_group]
  simp_rw [ht]; exact plate_tried x i j v |>.decode_second
end YM.Pert.First
