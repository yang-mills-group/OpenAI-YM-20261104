import YM.AlbaMS.Cutis.Shaper
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Native scalar lattice Green

Work with periodic matrices on the full torus. This does *not* install
a choice of zero photon mode in the orbifold Wick rule. Later use projection and
repeat large-period algebra. Use harmonic = means. For line algebra no FT
hypotheses. FT and derivative analysis use continuum symbols separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Loft Inlay Inlay.Net Odom Lattice
variable {n : Side}{R:Type*}
abbrev Vtx (n:Side):= Site n
abbrev Arm (n:Side):= Edge (Vtx n)
abbrev Cell (n:Side):=Matrix (Vtx n) (Vtx n) ℝ
variable (n)(i j : Axis)

-- period cases explicit.
def limo (y: Vtx n): Cell n:= Matrix.of fun x z=> if x+y=z then 1 else 0
abbrev del (i:Axis): Cell n:= limo n (step i)-1
-- mini bills for both sides, reuse for lap & Hessian
lemma limo_left {X:Type*}(T:Matrix (Vtx n) X ℝ)(y x z): (limo n y*T) x z=T (x+y) z:=by simp [Matrix.mul_apply, limo,ite_mul]
lemma limo_t (x:Vtx n): (limo n x)ᵀ=limo n (-x):=by
  ext i j; unfold limo; simp only [Matrix.transpose_apply, Matrix.of_apply]; by_cases ht:j+x=i<;> simp [ht,show i+-x=j ↔ j+x=i by constructor<;> rintro rfl<;>abel]
lemma limo_right {X:Type*}(T:Matrix X (Vtx n) ℝ)(y x z): (T*limo n y) x z=T x (z-y):=by nth_rw 1 [← transpose_transpose T]; nth_rw 1 [← neg_neg y]; rw [← limo_t, ← transpose_mul]; rw [sub_eq_add_neg]; exact limo_left n (Tᵀ) _ z x -- sub defeq
lemma limo_prod (x y:Vtx n): limo n x*limo n y=limo n (x+y) := by ext i j; rw [limo_left]; simp [limo,add_assoc]
lemma del_comm (x : Site n) : Commute (limo n x) (del n i):= .sub_right (show Commute (limo n x) (limo n _) by rw [Commute,SemiconjBy,limo_prod,limo_prod,add_comm]) (Commute.one_right _)
lemma dels : Commute (del n i) (del n j):= .sub_left (del_comm n _ _) (Commute.one_left _)
lemma dels_t : Commute (del n i)ᵀ (del n j):= by rw [del,transpose_sub, limo_t,transpose_one]; exact .sub_left (del_comm n _ _) (Commute.one_left _)
lemma delV (u: Vtx n→ℝ)(x:Vtx n): (del n i *ᵥ u) x=u (x+ step i)-u x:=by rw [del,sub_mulVec,one_mulVec]; simp [limo,Matrix.mulVec,dotProduct,ite_mul]

def lap : Cell n:= ∑ i:Axis,(del n i)ᵀ*del n i
lemma lap_sym : (lap n)ᵀ=lap n:=by simp only [lap,Matrix.transpose_sum, Matrix.transpose_mul, Matrix.transpose_transpose]
lemma commute_sum {X:Type*} (f : X→ Cell n)(v: Finset X)(k:Cell n)(h:∀ i∈v,Commute (f i) k): Commute (∑ i∈v,f i) k:=by
  change (∑ i∈v,f i)*k=k* ∑ i∈v,f i; rw [Matrix.sum_mul, Matrix.mul_sum]; exact Finset.sum_congr rfl h
lemma commute_lap : Commute (lap n) (del n i) := commute_sum _ _ _ _ (fun _ _=> Commute.mul_left (dels_t ..) (dels ..)) -- n arg
-- native average
abbrev fee (n:Side):ℝ:= (Fintype.card (Vtx n):ℝ)⁻¹
def mean (n:Side): Cell n:= Matrix.of fun _ _=> fee n
lemma mean_b (u : Vtx n→ℝ)(x): (mean n *ᵥ u) x=fee n * ∑ y:Vtx n,u y:=by rw [Finset.mul_sum];rfl
lemma fee_tick : 0<fee n:=by unfold fee; positivity
lemma fee_o : fee n*(Fintype.card (Vtx n):ℝ)=1:= inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne')
lemma mean_t : (mean n)ᵀ=mean n:=rfl
lemma mean_del : del n i*mean n=0:=by rw [del,Matrix.sub_mul, Matrix.one_mul]; apply sub_eq_zero.mpr; ext i j; exact limo_left ..
lemma mean_left : (del n i)ᵀ*mean n=0:=by rw [del,transpose_sub, limo_t, transpose_one, Matrix.sub_mul, Matrix.one_mul]; apply sub_eq_zero.mpr; ext i j; exact limo_left ..
lemma del_mean : mean n*del n i=0:=by nth_rw 1 [← mean_t]; nth_rw 1 [← transpose_transpose (del n i)]; rw [← transpose_mul, mean_left, transpose_zero]
lemma mean_power : mean n*mean n=mean n:=by
  ext i j; rw [Matrix.mul_apply]; change (∑ _: Vtx n, fee n * fee n)=_; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,mul_comm (Fintype.card (Vtx n):ℝ) (fee n),fee_o,one_mul]; rfl
lemma lap_mean : lap n*mean n=0:=by simp_rw [lap, Matrix.sum_mul,Matrix.mul_assoc, mean_del, Matrix.mul_zero, Finset.sum_const_zero]
-- graph nullity: scalar chain costs finite.
lemma wander (x:Vtx n) : (∑ i:Axis, (x i).val • (step i:Vtx n))=x:=by
  ext1 i; rw [Finset.sum_apply,Finset.sum_eq_single i]; simp only [Pi.smul_apply,step_apply, if_true,nsmul_eq_mul,mul_one]; exact ZMod.natCast_zmod_val .. -- fix
  intro j _ hj; simp [Ne.symm hj]; simp
lemma knell (v:Vtx n→ℝ)(h: ∀ i:Axis, del n i *ᵥ v=0): mean n *ᵥ v=v:=by
  have ht (i:Axis)(x) : v (x+step i)=v x:= sub_eq_zero.mp ((delV n i v x).symm.trans (congr_fun (h i) x))
  have hh (i:Axis)(x:Vtx n)(k:ℕ): v (x+k • step i)=v x:=by induction k with|zero=>simp|succ k ih=> rw [add_smul, one_smul, ← add_assoc, ht, ih]
  have hg (i:Vtx n): v i=v 0:=by
    suffices ∀ (s:Finset Axis), v (∑ x∈s, (i x).val • (step x:Vtx n))=v 0 from (congr_arg v (wander n i).symm).trans (this _)
    intro s; induction s using Finset.induction_on with|empty=>simp|@insert j s h ih=>rw [Finset.sum_insert h,add_comm, hh, ih]
  funext i; rw [mean_b]; simp_rw [hg _]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,fee_o,one_mul]
lemma parts (u: Vtx n→ℝ)(A: Cell n) : u ⬝ᵥ ((Aᵀ*A) *ᵥ u) = (A*ᵥu) ⬝ᵥ (A*ᵥu) :=by rw [← Matrix.mulVec_mulVec u,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
-- laps. don't need strict coercivity now.
lemma still (u: Vtx n→ℝ)(h: lap n *ᵥ u=0): mean n*ᵥu=u:=by
  have hh:u ⬝ᵥ (lap n *ᵥ u)=∑ i:Axis, (del n i *ᵥ u) ⬝ᵥ (del n i*ᵥ u):=by simp_rw [← parts]; simp_rw [lap,sum_mulVec,dotProduct_sum]
  rw [h, dotProduct_zero] at hh
  apply knell; intro i; rw [← dotProduct_self_eq_zero]; exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _=> (Finset.sum_nonneg (fun a _=> mul_self_nonneg _) : (0:ℝ) ≤ (del n i *ᵥ u) ⬝ᵥ (del n i*ᵥ u)))).1 hh.symm i (Finset.mem_univ _)

lemma massive_det : IsUnit (lap n+mean n).det:=by
  rw [← Matrix.isUnit_iff_isUnit_det,← Matrix.mulVec_injective_iff_isUnit];
  have hl:mean n*lap n=0:=by nth_rw 1 [← lap_sym,← mean_t]; rw [← transpose_mul, lap_mean,transpose_zero]
  refine (LinearMap.ker_eq_bot (f:=(lap n+mean n).mulVecLin) |>.mp ?_) -- fix
  rw [Submodule.eq_bot_iff]; intro x hx; change (lap n+mean n)*ᵥx=0 at hx; have hh:mean n *ᵥ x=0:=by nth_rw 1 [← mean_power]; nth_rw 1 [← zero_add (mean n*mean n)]; rw [← hl,← Matrix.mul_add, ← Matrix.mulVec_mulVec x, hx, mulVec_zero]
  rw [Matrix.add_mulVec,hh,add_zero] at hx; exact (still n x hx).symm.trans hh

def green (n:Side): Cell n:= (lap n+mean n)⁻¹-mean n
lemma green_sym : (green n)ᵀ=green n:=by simp only [green,transpose_sub, transpose_nonsing_inv, transpose_add, lap_sym, mean_t]
lemma lap_green : lap n*green n=1-mean n:=by
  let L:=lap n+mean n; have hm : L*mean n=mean n:=by unfold L; rw [Matrix.add_mul,lap_mean, zero_add,mean_power]
  have he : L*green n=1-mean n:=by rw [green, Matrix.mul_sub, Matrix.mul_nonsing_inv _ (massive_det n), hm]; -- rewrites?
  have ht : green n*L=1-mean n:=by nth_rw 1 [← green_sym]; nth_rw 1 [← show Lᵀ=L from by simp [L,lap_sym,mean_t]]; rw [← transpose_mul, he,transpose_sub,transpose_one,mean_t]
  have hv: green n*mean n=0:=by nth_rw 1 [← hm]; rw [← Matrix.mul_assoc, ht, Matrix.sub_mul, Matrix.one_mul,mean_power,sub_self]
  have hh: mean n*green n=0:=by nth_rw 1 [← mean_t,← green_sym]; rw [← transpose_mul,hv, transpose_zero]
  unfold L at he; rw [Matrix.add_mul, hh, add_zero] at he;exact he
lemma green_mean : green n*mean n=0:=by
  let L:=lap n+mean n; have he:L*mean n=mean n:=by unfold L; rw [Matrix.add_mul,lap_mean,zero_add,mean_power]
  have hx : L⁻¹* mean n=mean n:=by nth_rw 1 [← he]; rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul L (massive_det n), Matrix.one_mul]
  rw [green,Matrix.sub_mul,mean_power,hx,sub_self]
lemma green_del : Commute (green n) (del n i):=by
  let L:=lap n+mean n; let D:=del n i; have hh:Commute (mean n) D:= (del_mean n i).trans (mean_del n i).symm; have he: Commute L D:= (commute_lap n i).add_left hh
  refine Commute.sub_left (show Commute L⁻¹ D from ?_) hh; change L⁻¹ * D=D*L⁻¹; nth_rw 1 [← Matrix.mul_one D, ← Matrix.mul_nonsing_inv L (massive_det n)]; rw [← Matrix.mul_assoc D,← he, ← Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.nonsing_inv_mul L (massive_det n), Matrix.one_mul]
end YM.MSBar.Cutis.Winter
