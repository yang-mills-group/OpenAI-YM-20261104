import YM.PertExtension.Cosines
import YM.PertExtension.WedgeIdentity
import YM.PertExtension.OrbCovariance
import YM.PertExtension.SliceCurl

/-! The precise top projection in direction variables at even period. The singular
link inverse at zero is only used in a formula for curl response (exact-source
right hand side); no unscreened harmonic denominator asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.PertExtension.LatticePT
namespace Projection
open MeasureTheory Filter Maxwell Next Next.Rank.Perch Next.Rank.Radian Next.Rank Topology Set Real Metric Lattice Next.Rank.CellsInt
open Next.Rank.Beamer Orb Band Air Orbit
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical RealInnerProductSpace
local notation "ℑ" => Complex.I
variable {G : Gauge}{n : Side}

abbrev marked (i: Fin 4)(k:Site n) : ℂ := tone (step i) k-1
def gradient (k:Site n) : Ribbon := fun j=>marked j k
def backward (k:Site n) : Ribbon := fun i=> tone (-(step i)) k-1
lemma reverse_mark (i:Axis)(x:E4):star (increment i x) = increment i (-x):= by
   simp only [increment,readD, Pi.sub_apply,terrel,chimes,star_sub, Pi.one_apply,star_one]
   change starRingEnd ℂ (Complex.exp _)- _= _
   rw [show ∀ z:ℂ, starRingEnd ℂ (Complex.exp z)=Complex.exp (starRingEnd ℂ z) from fun z=> by rw [Complex.exp_conj]]; simp; norm_num; congr 1; rw [show starRingEnd ℂ (2:ℂ)=(2:ℂ) by exact map_ofNat ..] <;> ring
lemma tone_rev_wrap (n:Side) i (u:Cover):backward (wrap n u) i=increment i (-addr n u):= by
   unfold backward;rw [←show wrap n (-step i) = -step i from (map_neg ..).trans (congr_arg _ (wrap_step n i)),phase_matches]
   unfold increment readD; rw [Pi.sub_apply,terrel,terrel,chimes,chimes,inner_neg_left]
   rw [mapZ, show WithLp.toLp _ _= -basis i from ?_,inner_neg_right];rfl
   ext j; change (((( -(step i:Cover)) j :ℤ):ℝ) )= -(basis i j)
   simp [step_apply]
lemma tone_star {n:Side}(x k:Site n): tone (-x) k=star (tone x k):=by
  have hn : stdAddChar (N:=n.val) (-(∑ i,x i*k i)) = star (stdAddChar (∑ i,x i*k i)) := by
      change (↑(toCircle ( - (_ :ZMod n.val))):ℂ)= star (↑(toCircle ( (∑ i, x i*k i) : ZMod n.val)):ℂ)
      rw [AddChar.map_neg_eq_inv]; exact Circle.coe_inv_eq_conj _ -- Complex.inv_def? on Circle norm
  apply Eq.trans (congr_arg stdAddChar (show (∑ i,(-x) i*k i)= -∑ i,x i*k i from by simp only [Pi.neg_apply,neg_mul, Finset.sum_neg_distrib])) hn
lemma star_gradient (k:Site n)(j): backward k j=star (gradient k j):= by unfold backward gradient marked;rw [star_sub,star_one,tone_star]
lemma marked_sum (k:Site n): ∑ i:Axis,(gradient k i)*(backward k i)=(location (frequency k):ℝ) := by
   unfold gradient marked;simp_rw [tone_step];unfold location; rw [Complex.ofReal_sum]
   refine Finset.sum_congr rfl fun i _=>?_
   rw [star_gradient, Complex.sq_norm,gradient];simp_rw [marked,tone_step]
   exact Complex.mul_conj _
   -- goal uses star not starRingEnd

-- Fourier summation by parts. No complex conjugating the test signal.
variable {A : Links (Per n) ℂ}
private lemma shift_univ (f : Site n→ℂ)(i : Axis) : (∑ x:Site n,f (x+-step i))=∑ x:Site n,f x:= Equiv.sum_comp (Equiv.addRight (-step i)) f
lemma forward_price (k:Site n)(i)(f: Site n→ℂ): fourier (fun x=>f (x+step i)) k =tone (-step i) k * fourier f k:=by
  have he := shift_univ (fun x=>tone x k*f (x+step i)) i
  change ∑ x:Site n,tone (x+-step i) k * f (x+ -step i+step i)= _ at he
  change (∑ x:Site n,tone x k * f (x+step i))=_;rw [←he]
  simp only [neg_add_cancel_right, add_neg_cancel_right,tone_add]
  change _=tone (-step i) k * ∑ x:Site n,tone x k*f x;rw [Finset.mul_sum];exact Finset.sum_congr rfl fun _ _=>by ring

def current (A : Links (Per n) ℂ) (k:Site n)(i:Axis):=fourier (fun x=>A (x,i)) k
lemma fourier_add (k:Site n) (f g : Site n→ℂ):fourier (f+g) k=fourier f k+fourier g k:=by simp_rw [Band.fourier, Pi.add_apply,mul_add,Finset.sum_add_distrib]
lemma fourier_sub (k:Site n) (f g : Site n→ℂ):fourier (f-g) k=fourier f k-fourier g k:=by simp_rw [Band.fourier, Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
lemma forward_curl (k:Site n)(A:Links (Per n) ℂ) i j : fourier (fun x=>Curl A x i j) k= wedge (backward k) (current A k) i j :=by
  let f (i:Axis)(x:Site n):= A (x,i)
  have h : (fun x=>Curl A x i j)= (f i+fun x : Site n=>A (x+step i,j))-(fun x=> A (x+step j,i))-f j:= rfl
  rw [h,fourier_sub,fourier_sub,fourier_add]
  rw [forward_price (f:=fun x=>A (x,j)), forward_price (f:=fun x=>A (x,i))]; unfold wedge backward current f;ring
lemma curl_mode (k:Site n)(z:Ribbon)(x:Site n)(i j) : Curl (fun p: Edge (Site n)=> z p.2 * tone p.1 k) x i j = tone x k * wedge (gradient k) z i j := by simp only [wedge,Curl,tone_add,gradient,marked];ring -- typo

end Projection
end YM.PertExtension.LatticePT
