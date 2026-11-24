import YM.AlbaMS.Cutis.Sleek

/-!
# scalar codec Landau based using mean donor. Book.Fund and geometry equalities

Compressed Hessian from Lens. Identities derived before assigning representation
or matter insertions. The orthogonal projections use link root primal/transverse,
stays with deleted ghost cases. In mean lift `run` already subtracts over full
number of sites. Keep Volume implicitly normalized total area. Need parity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable {n : Side}{G:Gauge}
-- compression per gauge prescription
abbrev headD (n:Side) := (1/2:ℝ) • ((thorn n)ᵀ * mono n *thorn n)
abbrev gradD (n:Side) := (1/2:ℝ) • ((thorn n)ᵀ * bound n*shrub n true)
def run (n:Side):= shrub n true - mean n*shrub n true
-- base, normalization checked
abbrev longU (n:Side) := (thorn n)ᵀ* U n * (peg n)ᵀ
def wide (n:Side) := (1/2:ℝ) • ((thorn n)ᵀ * W n*thorn n)
def prop (n:Side) := gradD n*(longU n)ᵀ -- Def no assertion covariance pres
variable (h:Even n.val)
lemma head_t : (headD n)ᵀ=headD n:=by simp only [headD,transpose_smul,transpose_mul,transpose_transpose,mono_sym,Matrix.mul_assoc]
lemma wide_t : (wide n)ᵀ=wide n:=by simp only [wide,transpose_smul,transpose_mul,transpose_transpose,WT,Matrix.mul_assoc]
lemma peg_run : peg n*run n=1:=by rw [run,Matrix.mul_sub,← Matrix.mul_assoc,peg_mean, Matrix.zero_mul,sub_zero,petal]
lemma mean_run : mean n*run n=0:=by rw [run,Matrix.mul_sub,← Matrix.mul_assoc, mean_power,sub_self]
lemma flow_run : flow n*run n=run n:=by rw [run,Matrix.mul_sub,hedge,← Matrix.mul_assoc, low_mean]
lemma run_peg : run n * peg n=(1/2:ℝ) • (1+flow n)-mean n:=by
  rw [run,Matrix.sub_mul,Matrix.mul_assoc,meet,Matrix.mul_sub,Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,mean_low,mean_basis, smul_add (1/2:ℝ) (mean n) (mean n),← add_smul]; norm_num
lemma bound_run : bound n*run n=bound n*shrub n true:=by rw [run,Matrix.mul_sub, ← Matrix.mul_assoc, bound_mean, Matrix.zero_mul,sub_zero]
include h
lemma paidEta {E:Type*} (P:Matrix (Arm n) E ℝ)(hh:aura n*P=P): thorn n*((1/2:ℝ) •((thorn n)ᵀ*P))=P:=by rw [Matrix.mul_smul,← Matrix.mul_assoc,stalkRound h,Matrix.add_mul, Matrix.one_mul,hh,smul_add,← add_smul]; norm_num
lemma paid_inverse {E:Type*} (P:Matrix (Foil n) E ℝ): (1/2:ℝ) • ((thorn n)ᵀ* (thorn n*P))=P:=by rw [← Matrix.mul_assoc,stalkSeal h, Matrix.smul_mul, Matrix.one_mul,smul_smul]; norm_num
lemma thorns {E:Type*}{P T: Matrix (Foil n) E ℝ} (t:thorn n*P=thorn n*T): P=T:=by rw [← paid_inverse h P,t, paid_inverse h]
lemma heat : thorn n*headD n=mono n*thorn n:=by unfold headD; rw [Matrix.mul_assoc]; apply paidEta h; rw [← Matrix.mul_assoc,aura_mono, Matrix.mul_assoc, centerEq h]
lemma scope : thorn n*gradD n=bound n*shrub n true:=by unfold gradD; rw [Matrix.mul_assoc]; apply paidEta h; rw [← Matrix.mul_assoc, aura_bound, Matrix.mul_assoc, hedge]
lemma wing : thorn n*wide n=W n*thorn n:=by unfold wide; rw [Matrix.mul_assoc]; apply paidEta h; rw [← Matrix.mul_assoc,WW, Matrix.mul_assoc, centerEq h]
lemma scrape : pump n (mean n)* thorn n=0:=by
  have hm : pump n (mean n)*aura n= -pump n (mean n):=by nth_rw 1 [← aura_t,← show (pump n (mean n))ᵀ=pump n (mean n) from by simp only [pump,chip_t,mean_t]]; rw [← transpose_mul, high_mean,transpose_neg]; simp only [pump,chip_t,mean_t]
  have he : -(pump n (mean n)* thorn n)=pump n (mean n)* thorn n:=by rw [← Matrix.neg_mul, ← hm, Matrix.mul_assoc, centerEq h]
  ext i j; exact eq_zero_of_neg_eq (congr_fun (congr_fun he i) j)
lemma guest : (longU n)ᵀ * gradD n=1:=by simp_rw [longU,transpose_mul,transpose_transpose, Matrix.mul_assoc]; rw [scope h,← bound_run, ← Matrix.mul_assoc (U n)ᵀ,UL, Matrix.sub_mul, Matrix.one_mul, mean_run,sub_zero,peg_run]
lemma patch : thorn n * longU n=(1+aura n)*(U n* (peg n)ᵀ):=by rw [longU,← Matrix.mul_assoc,← Matrix.mul_assoc,stalkRound h, Matrix.mul_assoc]
lemma sub_entries : run n*(longU n)ᵀ=(U n)ᵀ*thorn n:=by
  have H : flow n * (U n)ᵀ=(U n)ᵀ*aura n:=by nth_rw 1 [← flow_t,← aura_t]; rw [← transpose_mul,← transpose_mul,UU]
  have he : mean n * (U n)ᵀ=0:=by nth_rw 1 [← mean_t]; rw [← transpose_mul, UM, Matrix.transpose_zero]
  rw [longU, transpose_mul,transpose_mul,transpose_transpose,transpose_transpose,← Matrix.mul_assoc,run_peg]; rw [Matrix.sub_mul,← Matrix.mul_assoc (mean n),he, Matrix.zero_mul,sub_zero, Matrix.smul_mul,Matrix.add_mul, ← Matrix.mul_assoc (flow n), H, Matrix.mul_assoc,centerEq h,Matrix.one_mul]; rw [smul_add,← add_smul]; norm_num
lemma touch_prop : thorn n*prop n= bound n* (U n)ᵀ * thorn n:=by rw [prop,← Matrix.mul_assoc,scope h, ← bound_run,Matrix.mul_assoc, sub_entries h,Matrix.mul_assoc]
lemma orth : (prop n)ᵀ=prop n:=by
  nth_rw 1 [← paid_inverse h (prop n)]; rw [touch_prop h, Matrix.transpose_smul]; rw [← paid_inverse h (prop n), touch_prop h]; congr 1; rw [transpose_mul, transpose_mul, transpose_mul,transpose_transpose,transpose_transpose, ← symmetryU]; simp only [Matrix.mul_assoc]
-- assert positivity later. tick.
lemma projective : prop n + wide n * headD n=1:=by apply thorns h; rw [Matrix.mul_add,touch_prop h, ← Matrix.mul_assoc,wing h, Matrix.mul_assoc (W n), heat h,← Matrix.mul_assoc (W n), W_hit,← Matrix.add_mul,projectionU,Matrix.sub_mul,scrape h,Matrix.one_mul, Matrix.mul_one, sub_zero]
lemma prop_image : prop n* longU n=longU n:=by rw [← orth h,prop]; rw [transpose_mul,transpose_transpose, Matrix.mul_assoc]; rw [show (gradD n)ᵀ*longU n=1 from ?_, Matrix.mul_one]; nth_rw 1 [← transpose_transpose (longU n),← transpose_mul]; rw [guest h,transpose_one]
lemma wide_grad : wide n * gradD n=0:=by apply thorns h; rw [← Matrix.mul_assoc,wing h,Matrix.mul_assoc,scope h,← Matrix.mul_assoc (W n), W_t, Matrix.zero_mul, Matrix.mul_zero]
lemma wide_null : wide n*prop n=0:=by rw [prop, ← Matrix.mul_assoc,wide_grad h, Matrix.zero_mul]
lemma prop_orto : prop n*wide n=0:=by nth_rw 1 [← orth h,← wide_t]; rw [← transpose_mul, wide_null h,transpose_zero]
lemma E_grad : headD n * gradD n=0:=by apply thorns h; rw [← Matrix.mul_assoc, heat h, Matrix.mul_assoc, scope h, ← Matrix.mul_assoc (mono n), mono_bound, Matrix.zero_mul, Matrix.mul_zero]
lemma self_pair : prop n* prop n=prop n:=by
  unfold prop; rw [Matrix.mul_assoc,← Matrix.mul_assoc (longU n)ᵀ, guest h, Matrix.one_mul]
-- full pass
lemma cash_A : thorn n * wide n *(thorn n)ᵀ= W n+W n* aura n:=by rw [wing h, Matrix.mul_assoc,stalkRound h,Matrix.mul_add, Matrix.mul_one]
lemma cash_C : thorn n*longU n*(run n)ᵀ= U n+aura n* U n:=by
  have he : longU n*(run n)ᵀ=(thorn n)ᵀ* U n:=by nth_rw 1 [← transpose_transpose (longU n)]; rw [← transpose_mul,sub_entries h, transpose_mul,transpose_transpose]
  rw [Matrix.mul_assoc,he, ← Matrix.mul_assoc,stalkRound h,Matrix.add_mul, Matrix.one_mul]
end YM.MSBar.Cutis.Winter
