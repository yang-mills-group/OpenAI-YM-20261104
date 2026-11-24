import YM.MSbar.Pole.Scale.Open

/-! # Mellin integrals in tensor meromorphic germs, an extra pole per sewing at most -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Mellin
open Momentum Ray Age Function Filter Set MeasureTheory Ambient
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I]
variable (A : Finset I) (d : Age) {F G : ℂ → Cloud I}

-- expand scale changes on each momentum sector of the graph
private lemma dry {R:ℝ} (h : Meridian (zone R) F) (n:ℕ) (k : ℕ) (x:External I n) {z} (hz : z∈zone R) :
    ContDiff ℝ ∞ (fun t:ℝ=> spill^[k] (augments A n F) z (t,x)) :=
    contDiff_iff_contDiffAt.mpr fun t=> (((terms Metric.isOpen_ball (puts h (B:=A) n) k).stream.smooth (z,t,x) ⟨hz,mem_univ _⟩).comp t
      (f:=fun i:ℝ=>(z,i,x)) (by fun_prop))
lemma carry {R:ℝ} (h : Meridian (zone R) F) (n:ℕ) (k : ℕ) (x y : External I n) {z:ℂ} (hz : z∈zone R) (c : ℂ) (a:ℝ)
    (hh : ∀ t:ℝ,G z n (move A t x)= c * F z n (move A (a*t) y)) :
    ∀ t:ℝ, (spill^[k] (augments A n G)) z (t,x) = c * (a:ℂ)^k * spill^[k] (augments A n F) z (a*t,y) := by
  induction k with
  | zero => intro t; simpa only [iterate_zero_apply,pow_zero,mul_one,augments] using hh t
  | succ k ih =>
    let D (u:ℝ):= (spill^[k] (augments A n F)) z (u,y); let b :ℂ:=c*a^k -- coerces a^k as real?
    have hd : ContDiff ℝ ∞ D := dry A h _ _ _ hz
    have hk(u:ℝ): HasDerivAt (fun w:ℝ=> (spill^[k] (augments A n G)) z (w,x)) (c*(a:ℂ)^(k+1)*deriv D (a*u)) u := by
      have hh:= (((hd.differentiable (by simp) _).hasDerivAt).scomp u (show HasDerivAt (fun t:ℝ=>a*t) a u by simpa using (hasDerivAt_id' u).const_mul a))
      have hl := (hh.const_mul (c*(a:ℂ)^k)).congr_of_eventuallyEq (Eventually.of_forall ih)
      refine hl.congr_deriv ?_; simp only [Complex.real_smul,pow_succ]; ring
    intro t; rw [iterate_succ_apply',iterate_succ_apply']; let b := c*(a:ℂ)^(k+1)
    -- t from integral over [0,1]; function subtraction gone
    change (∫ r:ℝ in Ioc 0 1, deriv (fun w:ℝ=> (spill^[k] (augments A n G)) z (w,x)) (r*t)) = b*∫ r :ℝ in Ioc 0 1, deriv D (r*(a*t))
    simp_rw [(hk _).deriv,mul_left_comm a _ t]; rw [integral_const_mul]

lemma area {n : ℕ} (z:ℂ)(x:External I n) : step A d F z n x =
    (∫ t : ℝ in Ioc (0:ℝ) 1, spill^[d.safety] (augments A n F) z (t,x)*(t:ℂ)^(d.alpha z-1+d.safety)) +
      ∑ i∈Finset.range d.safety,(d.increment i z)⁻¹*pbody A F i z n x := by
  unfold step room later eta; simp only [Pi.add_apply,Finset.sum_apply, alpha]; congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht=> ?_; congr 2 <;> ring

lemma finite_mul {R:ℝ} (h : Meridian (zone R) F) (n:ℕ) (x y : External I n) {z:ℂ} (hz : z∈zone R) (c : ℂ)
    (hh : ∀ t:ℝ,G z n (move A t x)= c * F z n (move A t y)) : step A d G z n x=c * step A d F z n y:= by
  have hp (i) (t : ℝ): spill^[i] (augments A n G) z (t,x)=c*spill^[i] (augments A n F) z (t,y):=by simpa using carry A h n i x y hz c 1 (by simpa using hh) t
  rw [area,area,mul_add]; congr 1
  · simp_rw [hp,mul_assoc,integral_const_mul]
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by unfold pbody; rw [hp,mul_left_comm]

def licensed {F : ℂ→Cloud I} (G : ℂ→Cloud I) (R:ℝ)(k:ℕ) := Meridian (zone R) G ∧ ∀ z∈slit R, ∀ n x,F z n x=(z^k)⁻¹*G z n x
lemma licence {l:ℕ} (h : Vortex l F) : ∃ R:ℝ, 0<R ∧ ∃ G:ℂ→Cloud I, licensed (F:=F) G R l:=by
  obtain ⟨R,W,hr,H,hh⟩:=h; refine ⟨R,hr,W,H,fun z hz n x=>?_⟩
  rw [← hh _ hz]; exact (inv_mul_cancel_left₀ (pow_ne_zero _ (show z≠0 from hz.2)) _).symm
lemma beyond {l:ℕ} (h : Vortex l F) : Vortex (l+1) (step A d F) := by
  obtain ⟨R,hr,G,H,hG⟩:= licence h; obtain ⟨r,P,hp,hP,ht⟩:= regular_open A d H hr
  refine ⟨min r R,P,lt_min hp hr,hP.mono (zone_le (min_le_left ..)),fun z hz n x=> ?_⟩
  have hm : z∈slit R:=⟨zone_le (min_le_right ..) hz.1,hz.2⟩; have hk := ht z ⟨zone_le (min_le_left ..) hz.1,hz.2⟩ n x
  rw [finite_mul A d H n x x hm.1 _ (fun _=>hG z hm n _),pow_add,mul_right_comm]
  rw [mul_left_comm,pow_one] -- check
  have hv : z≠0:=hz.2; rw [inv_mul_cancel_left₀ (pow_ne_zero l hv),mul_comm]; simpa using hk
end YM.MSbar.Pole.Mellin
