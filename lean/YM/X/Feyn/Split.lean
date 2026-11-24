import YM.X.Feyn.Stem
import YM.X.Gauss.Tide
import YM.PertExtension.OrbCovariance
/-!
Multilinear Feynman Gaussian on orbit and chart Cut Hessian. Pays exact tree projection through cut. Sign consistent with symmetric links.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set MeasureTheory Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb
open Pert.Orb (Potential positiveLinks takeLink wilson action)
open Series Series.Radial GaussianScore
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val)
local notation "E" => Potential G n
local notation "A" => Dir G n

def rwS (U:Config G n):=energy U/2
lemma faceS (a:E)(x:Site n)(i:PlaqAxes): faceValue (positiveLinks a) (x,i)=Pert.Orb.plaquette a x i.val.1 i.val.2:= by
    simp [posDir,negDir,Step.vec,← sub_eq_add_neg,faceValue,travel,Pert.Orb.plaquette,square,mul_assoc,Step.read,Step.used]; rw [add_right_comm x (step i.val.1),add_sub_cancel_right,add_sub_cancel_right]
lemma overS (a:E): wilson a= rwS (positiveLinks a):= by
    unfold wilson rwS energy; congr 1; rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i hi=>?_ ; simp_rw [faceS]; let v (a':Axis×Axis):= G.price (Pert.Orb.plaquette a i a'.1 a'.2)
    let w(a:Axis×Axis): Prop:= a.1<a.2; change _=∑ x:PlaqAxes, v x.val; rw [← Finset.sum_subtype {p:Axis×Axis| p.1<p.2} (by simp)] -- set syntax Finset?
    rw [Finset.sum_filter,Fintype.sum_prod_type]
lemma real_quadratic (a:E): jet (action G n) 2 a=Pert.Orb.form a a/2:= by
    have ht:= (Pert.Orb.jets_action (G:=G) (n:=n)).2.2 a a; unfold jet; rw [show (fun (_ : Fin 2)=> a) = ![a,a] from funext fun i=>by fin_cases i<;> rfl,ht]; norm_num [Nat.factorial]; ring
private lemma smooth_fix : ContDiff ℝ ω (Pert.Orb.fixing (G:=G) (n:=n)) := .div_const (.sum fun x _=> (contDiff_norm_sq ℝ).comp ((Pert.Orb.takeDiv x (G:=G) ).toContinuousLinearMap.contDiff)) _
lemma fix_quadratic (a:E): jet Pert.Orb.fixing 2 a= Pert.Orb.fixing a:= by
    rw [homogeneous_derivative Pert.Orb.fixing _ _ (smooth_fix.contDiffAt.of_le le_top)]
    have he : (fun r:ℝ=>Pert.Orb.fixing (r • a))=(fun r:ℝ=> r^2 * Pert.Orb.fixing a):= by
       funext r; simp only [Pert.Orb.fixing, map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,← Finset.mul_sum, mul_div_assoc]
    rw [he,iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]; simp [Nat.factorial]
lemma zero_fiscal {i:ℕ}(hi:i<2): jet (fiscal (G:=G) (n:=n)) i=0:= by
    funext x; interval_cases i
    · rw [jet_zero,fiscal_zero];rfl
    rw [homogeneous_derivative fiscal _ _ (fiscal_smooth.contDiffAt.of_le le_top),(fiscal_grades x).2,mul_zero];rfl
include he in
lemma cut_pow (p:E): Pert.Orb.form p p = Orb.score (cut p) (cut p)+2* Pert.Orb.fixing p:= by
   have hu : jet wilson 2 p= jet fiscal 2 (cut p):= by
      rw [show wilson = (rwS (G:=G)) ∘ positiveLinks from funext fun a=> overS a]; convert! tick_stem (G:=G) he p (f:=rwS) (fun t U=>by simp [rwS,energy_gauge]) _ fiscal_smooth.contDiffAt rfl (j:=2) (fun i h=> zero_fiscal h) 2 (by omega) using 1 
   have hh: ContDiffAt ℝ ω (wilson (n:=n) (G:=G)) 0:= by
       rw [show wilson = action G n - Pert.Orb.fixing from funext (fun a => Eq.symm (add_sub_cancel_right ..))]; exact Pert.Orb.diff_action.sub smooth_fix.contDiffAt
   have hk : jet (action G n) 2 p = jet wilson 2 p+jet Pert.Orb.fixing 2 p:= by
      unfold jet; rw [show action G n= Pert.Orb.wilson + Pert.Orb.fixing from rfl, iteratedFDeriv_add_apply (hh.of_le le_top) (smooth_fix.contDiffAt.of_le le_top),_root_.add_apply,mul_add]
   rw [real_quadratic,hu] at hk
   rw [Orb.second_jet, ← fix_quadratic]; linarith [hk]

def cost : Law E where
   P:= Pert.Orb.formL G n
   turns:= Pert.Orb.form_symm
   slope:= by
      obtain ⟨c,hc,h⟩:= quadratic_min (action G n) (fun a ha=> by rw [real_quadratic]; exact div_pos (Pert.Orb.form_pos ha) zero_lt_two); exact ⟨c,hc,fun a=>(h a).trans_eq (real_quadratic a)⟩
   smooth:= by
      have he : (fun x:E=> Pert.Orb.formL G n x x) = (fun x=>2 • jet (action G n) 2 x):= by funext x; rw [real_quadratic]; change Pert.Orb.form x x=_; rw [two_smul]; ring -- smul
      rw [he]; exact ((Gauss.Plausible.stamp (action G n) 2).smooth.continuous).const_smul (2:ℕ)
lemma covar_eq (i j: Module.Dual ℝ E): cost.wick i j=Pert.Orb.covar i j:= by
    unfold Law.wick Pert.Orb.covar; apply congr_arg j; apply (Pert.Orb.kernelEquiv G n).injective; rw [LinearEquiv.apply_symm_apply]; exact cost.applies i
end YM.PositionX.Feyn
