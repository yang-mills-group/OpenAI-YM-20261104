import YM.Pert.Align.Burst
import YM.Lattice.Foliation
/-!
Itinerary and uniform decay for toroidal gauge-fixed real scalar covariance. Whole physical period itinerary. Use existing Pert.Fourier estimates: seam distances on torus; no need periodization from cover estimate at large distance.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval
open Function Filter Set MeasureTheory Metric Finset Lattice Pert Pert.Align Pert.Full
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {T : Type*} {n : Lattice.Side}
local notation "L"=> Lattice.lift

def green (x:Site n): ℝ:= (toroid x).re
section difference
variable {V : Type*} [AddCommGroup V] {E : Type*} [AddCommGroup E] [One E]
def differ (i:Axis)(f: Four E→V)(x):= f (x+step i)-f x
def grads : List Axis → (Four E→V) → (Four E→V)
 | [], f=> f
 | i::d,f=> differ i (grads d f)
end difference
variable (D:List Axis) (z:Site n)
private lemma job_raw : Band.joint 1 D (n:=n)=grads D toroid:= by
   funext z; induction D generalizing z with
   | nil=> rw [grads]; simp_rw [Band.joint,Band.claw,toroid,List.map_nil,List.prod_nil,mul_one];simp [mul_comm]
   | cons i k h=> rw [grads,differ,← h,←h]; simp_rw [Band.joint,Complex.ofReal_one,one_zpow,one_mul,← Finset.sum_sub_distrib, Band.claw,char_add]; refine Finset.sum_congr rfl fun a _=> ?_; simp only [List.map_cons,List.prod_cons];ring
lemma jobs_base : (Band.joint 1 D z).re=grads D green z:= by
   rw [job_raw]; induction D generalizing z with
   | nil=> rfl
   | cons i k hi=>simp_rw [grads,differ,Complex.sub_re,hi]
lemma raw_pay {r:ℝ}(hr:0 < r): (Band.joint r D z).re*((r:ℝ)^(2+D.length))=grads D green z:= by
   rw [← jobs_base]
   have hx : Band.joint r D z=(r^(2+D.length):ℝ)⁻¹ • (Band.joint 1 D z):= by
      unfold Band.joint;rw [Complex.ofReal_one,one_zpow,one_mul,Complex.real_smul]; apply congr_arg (fun x:ℂ=>x*_); rw [Complex.ofReal_inv,zpow_neg,Complex.ofReal_pow,show ((r:ℂ) ^ ((D.length:ℤ)+2)) = (r:ℂ)^(2+D.length) from (by rw [Nat.add_comm 2]; norm_cast)]
   rw [hx]; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; change ((r^(2+D.length):ℝ)⁻¹ * _)*_= _; field_simp
lemma princ : (pdist z:ℝ) ≤ ‖incVec 1 (L z)‖ := by
   obtain ⟨i,hi,h⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ (α:=Axis)) (f:=fun i=>(lift z i).natAbs) Finset.univ_nonempty
   rw [pdist, h]; convert! Band.coordinate_le (incVec 1 (lift z)) i using 1; simp only [Full.incVec_apply,one_mul,← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
lemma radius : ‖incVec 1 (L z)‖≤ (n.val:ℝ):= by
   obtain ⟨i,hi⟩:= Band.max_coord (incVec 1 (lift z)); apply hi.trans; have hz:= lift_centers z i; have ht : 2*(L z i).natAbs≤n.val:= by omega
   simp only [Full.incVec_apply,one_mul, ← Int.cast_abs, Int.abs_eq_natAbs,Int.cast_natCast]; exact_mod_cast ht

-- decay off fixed site ball. choose h accordingly. no finite-volume recurrence.
lemma rate : ∃ (C:ℝ)(R:ℕ), C≥0 ∧ ∀ {n:Side}(z:Site n), R< pdist z → |grads D green z|≤ C/(pdist z:ℝ)^(2+D.length):= by
   obtain ⟨C,hC,H⟩:= Band.upper_tail D 1 zero_lt_one
   let s:ℝ:=2 * Real.pi * (D.length + 4:ℕ); have hs:0<s:= by unfold s; positivity
   obtain ⟨R,hR⟩:= (exists_nat_ge (2*s)) -- obtain choose?
   let M:= Band.purse*s^(D.length+2); refine ⟨C/s+M,R,add_nonneg (by positivity) (by unfold M Band.purse; positivity),fun {n} z he=>?_⟩
   let k:ℝ := pdist z; have h₁ : (R:ℝ)<k:= by unfold k;exact_mod_cast he
   have hk:0<k:= by have:= hR.trans_lt h₁; linarith
   let h:= k⁻¹; have hh:0<h:=by unfold h; positivity
   have hi: h*s ≤ 1/2:= by unfold h; rw [inv_mul_eq_div]; rw [div_le_iff₀ hk]; linarith [hR.trans h₁.le]
   have hv : mesh n*(D.length+4:ℕ)≤h*s:= by unfold mesh h; rw [inv_mul_eq_div,div_mul_eq_mul_div]; unfold s; exact div_le_div_of_nonneg_left (by positivity) hk ((princ z).trans (radius z))
   have hz : 1≤‖incVec h (L z)‖:= by rw [show incVec h (L z)=h • incVec 1 (L z) from PiLp.ext (fun i=> by simp), norm_smul,Real.norm_of_nonneg hh.le]; unfold h; rw [inv_mul_eq_div, le_div_iff₀ hk,one_mul]; exact princ z
   let f:= Band.piece h s D z; let g:=Band.joint h D z
   have hG : ‖g‖ ≤ C/s+M := ( (norm_add_le (g-f) f)|>.trans (add_le_add (H hh hs hi hv _ hz) (Band.lower h s hs hh (by linarith) z D))) |> fun H=> (by rwa [sub_add_cancel] at H)
   rw [← raw_pay D z hh, abs_mul, abs_of_pos (pow_pos hh _), div_eq_mul_inv]; unfold h; rw [inv_pow]; exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hG) (by positivity)
end YM.PositionX.Interval
