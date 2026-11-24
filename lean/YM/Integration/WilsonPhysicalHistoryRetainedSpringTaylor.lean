import YM.Integration.WilsonPhysicalHistoryRetainedSpringLength
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSample
import YM.Integration.FundedCurvatureRayTaylor

/-! The real-coupling remainder of the full previous curvature field at one
original site, including all rotations and its complete commissioned series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Wilson Precision Exterior Work.F03 Bid
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {k : ℕ}

def siteTaylor (A : ℕ→Atom G k) (x : Site n) (z : Dir G n) (q : ℕ) (t : ℝ) : ℂ :=
  ((Fintype.card Signed:ℂ)⁻¹) * ∑ s : Signed,∑' i,FundedCurvatureRayTaylor.polynomial
    (A i) x (collect G (pulled z s)) q t

theorem row_taylor (A : ℕ→Atom G k) {σ C : ℝ} (hs : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (v : Directions G n)
    {M : ℝ} (pos : 0≤M) (bound : ∀ i,FundedCurvatureRayTaylor.Available (A i) x v M)
    (q : ℕ) (t : ℝ) :
    ‖(∑' i,((A i).unmasked (WilsonMeasuredPathTaylor.field v t) x:ℂ)) -
      ∑' i,FundedCurvatureRayTaylor.polynomial (A i) x v q t‖≤C*(2*M*|t|/σ)^(q+1) := by
  let u (i : ℕ) : ℂ := (A i).unmasked (WilsonMeasuredPathTaylor.field v t) x
  let p (i : ℕ) := FundedCurvatureRayTaylor.polynomial (A i) x v q t
  let b : ℝ := (2*M*|t|/σ)^(q+1)
  have hb : 0≤b := by dsimp only [b]; positivity
  have full (i : ℕ) : ‖u i‖≤(A i).budget σ*2^k := by
    rw [show ‖u i‖=|(A i).unmasked (WilsonMeasuredPathTaylor.field v t) x| from Complex.norm_real _]
    exact ((A i).unmasked_bound _ _).trans (mul_le_mul_of_nonneg_right
      ((A i).lower_budget σ hs) (by positivity))
  have fu : Summable u := (Summable.of_nonneg_of_le (fun i=>norm_nonneg (u i)) full
    (paid.2.1.mul_right _)).of_norm
  have each (i : ℕ) : ‖u i-p i‖≤(A i).budget σ*b := (FundedCurvatureRayTaylor.original
    (A i) x v pos (bound i) q t).trans (length_taylor (A i) hs pos q t)
  have normed := Summable.of_nonneg_of_le (fun i=>norm_nonneg (u i-p i)) each (paid.2.1.mul_right b)
  have fp : Summable p := by simpa only [Pi.sub_apply,sub_sub_cancel] using fu.sub normed.of_norm
  change ‖(∑' i,u i)-(∑' i,p i)‖≤C*b
  rw [←fu.tsum_sub fp]
  apply (norm_tsum_le_tsum_norm normed).trans ((normed.tsum_le_tsum each (paid.2.1.mul_right b)).trans ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right paid.2.2 hb

theorem rooted_taylor (A : ℕ→Atom G k) {σ C : ℝ} (hs : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (z : Dir G n)
    {M : ℝ} (hm : 0≤M) (bound : ∀ (s : Signed) (i : ℕ),
      FundedCurvatureRayTaylor.Available (A i) x (collect G (pulled z s)) M)
    (q : ℕ) (t : ℝ) :
    ‖(sitePacket A x (represent (t • z)):ℂ)-siteTaylor A x z q t‖ ≤
      C*(2*M*|t|/σ)^(q+1) := by
  have repre (s : Signed) : pull s 0 (represent (t • z))=
      WilsonMeasuredPathTaylor.field (collect G (pulled z s)) t := by
    rw [Work.F03.represent_pulled]
    funext e
    rw [Work.F03.represent_link]
    rfl
  let u (s : Signed) := ∑' i,((A i).unmasked (WilsonMeasuredPathTaylor.field
    (collect G (pulled z s)) t) x:ℂ)
  let p (s : Signed) := ∑' i,FundedCurvatureRayTaylor.polynomial (A i) x (collect G (pulled z s)) q t
  have fact : (sitePacket A x (represent (t • z)):ℂ)-siteTaylor A x z q t=
      (Fintype.card Signed:ℂ)⁻¹ * ∑ s : Signed,(u s-p s) := by
    simp only [sitePacket,Patch.average,siteTaylor,repre,Complex.ofReal_mul,Complex.ofReal_sum,
      Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_tsum,u,p,Finset.sum_sub_distrib,mul_sub]
  rw [fact,norm_mul,norm_inv,Complex.norm_natCast]
  have card : 0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum
    (g:=fun _=>C*(2*M*|t|/σ)^(q+1)) fun s _=>row_taylor A hs paid x _ hm (bound s) q t))
    (inv_nonneg.mpr card.le)).trans_eq
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ card.ne',one_mul]

end YM.Integration.OriginalMarkedRunAction
