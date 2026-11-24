import YM.AnalyticNext.QUARTIC_MATCH.Radius.Gradient
/-! # Extend compiled page.First to loops in true raw LOG coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open Estimate Estimate.Purse Estimate.Village Estimate.Logfee Estimate.Plaque Joint Local Local.Wages  Local.Rotate
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Fetch
open Polish
open Green (wt)


variable {α K : Type*} {G : Gauge} {n l c f : Side}

def nearCost (G:Gauge)(m:ℕ)(σ Λ:ℝ):= (2^m * gratuity G (down σ m) m)^2 * Λ
-- local
variable {p : Clip} {W : PathData G} {σ C Λ} (h : W.Bounds p σ C Λ)
def byLoop (W : PathData G) (x : Site n) (a : Dir G n) := Patch.average fun s : Signed=> atend W.loop (s⁻¹.act x) (shifts s 0 a)
lemma byKey (W : PathData G)(a : Dir G n):loop W (represent a)=∑ x,byLoop W x a:=by
  have hh (s : Signed) := Equiv.sum_comp (s⁻¹.actEquiv (R:=Per n)).toEquiv (fun x => atend W.loop x (shifts s 0 a))
  unfold Precision.loop byLoop Patch.average
  rw [← Finset.mul_sum,Finset.sum_comm]
  apply congr_arg; refine Finset.sum_congr rfl fun i _ => ?_; simp only [← rep_shifts]; exact hh i|>.symm
include h
lemma key_rate (x:Site n)(a:Dir G n): ContDiffAt ℝ ω (byLoop W x) a:= contDiffAt_const.mul (ContDiffAt.sum fun s _ => (atend_rate _ h.width h.two (s⁻¹.act x) (shifts s 0 a)).comp a (shifts s (0:Site n)).contDiff.contDiffAt)
variable {m:ℕ}
private lemma stationLoop {ι:Type*} [DecidableEq ι]{d : ι→Dir G n} (x : Dir G n) (hp : ‖x‖<1) (S : Finset ι) (hm : S.card ≤ m)
    (P : Estimate.Purse ι (Site n)) (hh : Linkbill 1 P d) (he : tollRate P 1 (down σ m)) : P.Jets S d
      (atend W.loop) x (nearCost G m σ Λ) := by
  let t := down σ m; let u := gift G t m; let a := 2^m*gratuity G t m
  have ht : 0<t := Estimate.down_pos m h.width
  have hq : 5*m*t ≤ σ*((1:Side).val:ℝ) := by simpa only [t,PNat.val_ofNat,Nat.cast_one,mul_one] using uses_down m h.width
  have he' (B) (T) (h' : T⊆S) := post_pop hh he ht.le T _ ((Finset.card_le_card h').trans hm) x hp.le B
  have hu : 0≤u := (gift_pos ..).le
  exact atom_budget W.loop hh he ht x hp S m hm hq u he' hu h.width h.two
lemma nextLoop (k : ℕ) (hm : k ≤ m) (x : Dir G n) (hp : ‖x‖<1) (z : Site n) :
    Costs (trials G (down σ m) z) (budget ℝ) (byLoop W z) x k (Real.exp (2*down σ m)^m*nearCost G m σ Λ) := by
  intro d c hc; let t := down σ m; let P : Purse (Fin k) (Site n) := Local.Wages.account 1 none (fun _=>z) (fun _=> -t) c (fun i => (hc i).1)
  let u (i : Fin k) (p : Site n) : ℝ := P.toll i p
  have ht : 0<t := down_pos m h.width
  have hu i y : u i y=(wt t y z)⁻¹ := by simp [u,P,Wages.account, Green.wt, Real.exp_neg]
  have hf : tollRate P 1 t := Wages.travels _ _ _ _ _ _ (fun _ => by rw [abs_neg,abs_of_nonneg ht.le])
  have he : Linkbill 1 P d := by
    intro i j; refine ⟨by positivity,fun _ y => ?_,fun he => ?_⟩
    · rw [Purse.price, Finset.prod_singleton,Purse.target, Finset.prod_singleton]
      rw [show P.toll i y=_ from hu i y,inv_mul_eq_div]; simp only [PNat.val_ofNat,Nat.cast_one,inv_one, one_mul]
      exact (div_le_iff₀ (Green.wt_pos ..)).mpr ((hc i).2 (y,j))
    simp [P, Wages.account, Purse.tagged] at he
  let f s (x : Site n) (a : Dir G n) := atend W.loop (s⁻¹.act x) (shifts s 0 a)
  let a := Real.exp (2*down σ m)^m*nearCost G m σ Λ; let S : Finset (Fin k) := Finset.univ
  have hM : S.card≤m := by simpa [S] using hm
  have hb (s : Signed) : P.Jets S d (f s) x a := by
    have hv := stationLoop h (shifts s 0 x) (lt_of_le_of_lt (shift_le s x) hp) _ hM _ (bonds s hf ht.le he) (stays s hf)
    refine ((Rotate.restores s hv).mono (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp (by positivity)) hM) hv.1)).under fun i => ?_
    have ht : bill S d (f s i) x=bill S (shifts s 0 ∘ d) (atend W.loop (s⁻¹.act i)) (shifts s 0 x) := by
      unfold bill; rw [show f s i=_ from (show f s i=atend W.loop (s⁻¹.act i) ∘ shifts s 0 from rfl)]
      exact lin_rate_at _ _ _ (atend_rate _ h.width h.two (s⁻¹.act i) _) _ _
    exact (congr_arg (‖·‖) ht).le
  let w (i : Site n) z := ∑ s : Signed, f s i z
  have hh (s i) : ContDiffAt ℝ ω (f s i) x := (atend_rate _ h.width h.two (s⁻¹.act i) (shifts s 0 x)).comp x (shifts s (0:Site n)).contDiff.contDiffAt
  have hw i : ContDiffAt ℝ ω (w i) x := ContDiffAt.sum fun s _ => hh s i
  unfold Polish.budget
  rw [← Estimate.univEstimate _ _ _ (key_rate h z _)]
  have hv : P.Jets S d (byLoop W) x a := by
    apply (Jets.rate (Jets.allotted Finset.univ f (fun s _ i => hh s i) (fun s _ => hb s)) _ hw).mono
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact le_of_eq (by rw [abs_of_nonneg (by positivity)]; field_simp)
  have hU := hv.2.1 (show ¬P.tagged S from by simp [P,Purse.tagged,Wages.account]) z
  rw [show P.price S z=1 by simp [Purse.price,P,Wages.account,Green.wt],one_mul] at hU
  exact hU
end Fetch
end YM.AnalyticNext.QuarticMatch.Radius
