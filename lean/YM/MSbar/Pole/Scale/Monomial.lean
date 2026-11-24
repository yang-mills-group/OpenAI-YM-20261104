import YM.MSbar.Pole.Scale.Hover
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Ribbons with engineering power and logarithms

These bind the pole-order calculation to geometry. `Mono` tests positions and momentum rays
infinitesimally rescaled. No log dependence excluded before propagation. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] (A : Finset I) (a : ℤ)

inductive Ledger : (ℝ → Cloud I) → Prop
| zero : Ledger 0
| line (k: ℕ) {H:Cloud I} (c:ℂ): Canonical H →
    Ledger (fun r n x=> (r:ℂ)^a * (Real.log r:ℂ)^k * c * H n (move A r x))
| merge {F G} : Ledger F → Ledger G → Ledger (F+G)

variable {A a}
private lemma zpower (r : ℝ) (hr:0<r) (a:ℤ) : ContDiffAt ℝ 1 (fun x:ℝ=>(x:ℂ)^a) r:=by
  cases a with
  | ofNat n => change ContDiffAt ℝ 1 (fun x:ℝ=>(x:ℂ)^((n:ℕ):ℤ)) r; simp only [zpow_natCast]; exact Complex.ofRealCLM.contDiff.contDiffAt.pow n
  | negSucc n =>
    simp only [zpow_negSucc]; refine ContDiffAt.inv ?_ ?_
    · exact Complex.ofRealCLM.contDiff.contDiffAt.pow _
    exact pow_ne_zero _ (by exact_mod_cast hr.ne')
theorem Ledger.smooth {F} (h : Ledger A a F) {r : ℝ} (hr:0<r) (n) (x) : ContDiffAt ℝ 1 (fun s=> F s n x) r:= by
  induction h with
  | zero=> exact contDiffAt_const
  | line k c hf=>
    have hp := zpower r hr a
    refine ContDiffAt.mul (ContDiffAt.mul ?_ contDiffAt_const) ?_
    · exact hp.mul (((Complex.ofRealCLM.contDiff.contDiffAt.comp r (Real.contDiffAt_log.mpr hr.ne')).pow k))
    exact ((hf.2 n).localn 1 (mem_univ _)).comp r (((curve_diff A x).of_le (by norm_cast)).contDiffAt)
  | merge _ _ ih ih'=> exact ih.add ih'

namespace Curtain
variable (A) (d:Age)
def evaluate (m : ℕ)(H : Cloud I) (E : ℂ→ℂ) (r : ℝ)(z : ℂ)(n:ℕ)(x:External I n):=
    (r:ℂ)^d.a * (Real.log r:ℂ)^m * E ((Real.log r:ℂ)*z) * H n (move A r x)

lemma silk (m : ℕ) {H : Cloud I} (h:Canonical H) {E : ℂ→ℂ} (he : Differentiable ℂ E) :
    Soft (fun r z n x=> evaluate A d m H E r z n x):=by
  refine ⟨fun r hr=>?_,fun r hr n x=>?_⟩
  · apply regular_swirl (hr:=zero_lt_one)
    let P (z:ℂ):= (r:ℂ)^d.a * (Real.log r:ℂ)^m * E ((Real.log r:ℂ)*z)
    have hp : Differentiable ℂ P := by unfold P; fun_prop
    convert (singleMove A r (R:=1) h.constant).weight hp 1 (fun x hx=> ((zone_mem ..).mp hx).le) using 1
    funext z n x; exact mul_comm ..
  refine ⟨fun p:ℝ × ℂ=> evaluate A d m H E p.1 p.2 n x,?_,Eventually.of_forall fun _ _=>rfl⟩
  unfold evaluate
  have hf : ContDiffAt ℝ 1 (fun x:ℝ× ℂ=>(Real.log x.1:ℂ)) (r,0) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (ContDiffAt.log contDiffAt_fst hr.ne')
  have hg : ContDiff ℝ 1 E:= he.contDiff.restrict_scalars ℝ
  apply ContDiffAt.mul
  · refine ContDiffAt.mul ?_ (hg.contDiffAt.comp _ (hf.mul contDiffAt_snd))
    refine ContDiffAt.mul ?_ (hf.pow _)
    exact (zpower r hr d.a).comp (r,(0:ℂ)) (f:=Prod.fst) contDiffAt_fst
  exact ((h.2 n).localn 1 (mem_univ _)).comp (r,(0:ℂ)) (f:=fun x':ℝ × ℂ=>move A x'.1 x) (((curve_diff A x).of_le (by norm_cast)).contDiffAt.comp _ contDiffAt_fst)

variable {A d}
def polar (k : ℕ) (F:ℕ→ℝ→ Cloud I) (r : ℝ) := purePolar k (fun i=> F i r)

lemma raised (k : ℕ) (m : ℕ) {H : Cloud I} (h:Canonical H) {E : ℂ→ℂ} (he : Differentiable ℂ E) (A:Finset I) (d:Age) :
    ∃ C : ℕ→ℝ→Cloud I,(∀ i, Ledger A d.a (C i)) ∧
       Soft ((fun r z n x=> z⁻¹^k * evaluate A d m H E r z n x)-polar k C) := by
  induction k generalizing m E with
  | zero =>
    refine ⟨0,fun _=> Ledger.zero,?_⟩
    apply Soft.backside (silk A d m h he); intros; funext n x; simp [polar]
  | succ k ih =>
    let T:= dslope E 0
    have ht: Differentiable ℂ T:= differentiableOn_univ.mp <| (Complex.differentiableOn_dslope univ_mem).mpr he.differentiableOn
    have hy (z:ℂ) : E z = E 0 + z * T z:= by
      by_cases hv:z=0
      · subst z; simp
      rw [show T z = _ from dslope_of_ne E hv]; simp only [slope_def_module,sub_zero,smul_eq_mul,mul_inv_cancel_left₀ hv]; ring
    obtain ⟨C,hc,hq⟩:= ih (m+1) ht
    let D : ℝ→Cloud I:=fun r n x=> (r:ℂ)^d.a * (Real.log r:ℂ)^m * E 0 * H n (move A r x)
    let W := Function.update C k D
    refine ⟨W,fun i=>?_,Soft.backside hq ?_⟩
    · by_cases he:i=k
      · subst i; simpa [W] using Ledger.line (A:=A) (a:=d.a) m (E 0) h
      simpa [W,he] using hc i
    intro r z hr hz; funext n x
    change z⁻¹^k*_ - polar k C r z n x= z⁻¹^(k+1)*_ - purePolar (k+1) _ z n x
    rw [purePolar_up,ext_cut k _ (fun i=> C i r) (fun i hi=> congr_fun (update_of_ne hi.ne _ _) _)]
    simp only [Pi.add_apply, W, Function.update_self, Pi.smul_apply,smul_eq_mul]; unfold evaluate polar D
    rw [hy ((Real.log r:ℂ)*z)]; push_cast; rw [pow_succ, pow_succ z⁻¹]; field_simp; ring
end Curtain
end YM.MSbar.Pole
