import YM.Trace.Fock.Singleton
import Mathlib.Algebra.Polynomial.Roots
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.Trace.Shell
open scoped Topology ContDiff Pointwise Polynomial
open YM Filter MeasureTheory Boundary Function Complex Polynomial
def onLine {m:ℕ} (a : polySlot m→ℂ) (p : Mom) : ℂ[X] := ∑ i, monomial i.1.val (a i * slotPolynomial i p)
lemma onLine_eval {m:ℕ} (a : polySlot m→ℂ) (p : Mom) (t : ℝ) : (onLine a p).eval (t:ℂ)=slotPacket a (t • p) := by
  unfold onLine slotPacket; simp only [eval_finset_sum,eval_monomial,slotPolynomial_dilate,Complex.ofReal_pow]; apply Finset.sum_congr rfl (fun i _=>by ring)
lemma chokeLine {m} (a b : polySlot m→ℂ) (he : ∀ p : Mom, slotPacket b p=(‖p‖:ℂ) * slotPacket a p) (p : Mom) : slotPacket b p = 0 := by
  let h := onLine b (-p)
  let g := C (‖p‖:ℂ) * onLine a (-p)
  have hEq (t : ℝ) : h.eval (t:ℂ)= (Complex.ofReal |t|) * g.eval (t:ℂ) := by
    rw [show h = _ from (rfl : h=onLine b (-p)),show g=C _ * _ from rfl,onLine_eval,he,norm_smul,norm_neg,ofReal_mul,Real.norm_eq_abs, eval_mul,eval_C,onLine_eval]; ring
  have hE : h=X*g := by
    apply sub_eq_zero.mp
    refine (h-X*g).eq_zero_of_natDegree_lt_card_of_eval_eq_zero (ι:=Fin ((h-X*g).natDegree+1)) (f:=fun i=>((i:ℕ):ℂ)+1) ?_ ?_ (by simp)
    · rintro a b h; apply Fin.ext; exact Nat.cast_inj (R:=ℂ) |>.mp (add_right_cancel h)
    rintro i; simp only [eval_sub,eval_mul,eval_X]; exact sub_eq_zero.mpr (by simpa [abs_of_nonneg (show (0:ℝ)≤ (i:ℝ)+1 by positivity)] using hEq ((i:ℝ)+1))
  have hub := hEq (-1); have hlb : h.eval (-1) = -g.eval (-1) := by rw [hE, eval_mul,eval_X, neg_one_mul]
  simp only [abs_neg,abs_one,ofReal_one,one_mul,ofReal_neg] at hub hlb
  have ht : h.eval (-1) = 0 := by linear_combination (hub + hlb)/2
  rw [show (-1:ℂ) = ↑(-1:ℝ) by push_cast; rfl, show h.eval ↑(-1:ℝ) = _ from onLine_eval _ _ _] at ht; simpa using ht
lemma pureZero {N : ℕ} (f : Mom→ℂ) (hc : Control N f) (h : ∀ ψ : Test4, Eligible ψ → (∫ p, Probe.hat ψ (ray p) * f p ∂ν)=0) : f=ᶠ[ae ν] (0:Mom→ℂ) := by
  have hz : Control N (0:Mom→ℂ) := ⟨aestronglyMeasurable_const (b:=0), by simpa [Pi.zero_apply] using integrable_const (c:=fun x=> (0:ℂ))⟩ -- integrable_zero over sigma
  obtain ⟨m,hm⟩:=bounded_two_bare_packets N
  rcases hm f 0 hc hz (fun ψ hψ=> by rw [h ψ hψ]; simp) 0 with ⟨a,ha⟩
  rcases hm f 0 hc hz (fun ψ hψ=> by rw [h ψ hψ]; simp) 1 with ⟨b,hb⟩
  have hEq : slotPacket b=ᶠ[ae volume] fun p=> (‖p‖:ℂ)*slotPacket a p := by
    filter_upwards [ha,hb, (ae_iff.mpr (by simp) : ∀ᵐ (p:Mom),p≠0)] with p ha hb hp
    have : (‖p‖:ℂ) ≠0 := by norm_cast; simpa
    rw [← ha,← hb]; dsimp [bare]; norm_num; field
  unfold ν; refine withDensity_absolutelyContinuous _ _ (hb.mono fun p hp=> ?_)
  rw [chokeLine _ _ (by exact congrFun (((slotPacket_cont b).ae_eq_iff_eq _ ((by fun_prop) : Continuous _)).mp hEq)) p] at hp
  dsimp [bare] at hp; norm_num at hp; exact hp
end YM.Trace.Shell
