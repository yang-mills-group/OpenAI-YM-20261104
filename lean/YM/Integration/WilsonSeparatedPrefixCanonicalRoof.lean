import YM.Integration.WilsonSeparatedPrefixCanonicalHeard
import YM.Integration.WilsonThermometerSameWalkSectionFare

/-! The duplicated constant convolution cancels its terminal wallet on each
proper face. Only the original seats are cleared in the physical answer. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalRoof
open Function Filter Set Finset Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Lodestar
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

def front (I:Type)[Fintype I][DecidableEq I]:ℝ:=
  (Fintype.card (Marks I).Mode:ℝ)*(49*4*4^(Fintype.card I)*((Fintype.card I:ℝ)^(Fintype.card I)))

private theorem aperture (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠ i:ℕ in atTop,((A).params i).columns ≤ (H i)^2:=by
  obtain ⟨a,ha⟩:=eventually_atTop.mp (WilsonRegisteredLogFare.column R simple pace.2)
  filter_upwards [eventually_ge_atTop (a+1),(RG01.Physical.hats simple (A)).eventually_ge_atTop 2] with i ready hi
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have h:=ha j (by omega)
  have log:=Real.log_le_self (x:=H (j+1)) (by linarith)
  nlinarith only [h,log,hi,mul_nonneg (sub_nonneg.mpr hi) (show 0≤H (j+1) by linarith)]

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit) :
    ∀ᶠ j:ℕ in atTop,∀k l L:ℕ,j≤k+1 → l≤L → ∀w:I → ℝ,(∀i,0<w i) →
    (∑t:(Marks I).Mode,Poly.toll w t*WilsonSeparatedPrefixCanonicalHeard.roof R w t k j l)≤
      front I*(H (k+1))^(6+(4+6*L)*Fintype.card I+6*(k+1-j)*Fintype.card I):=by
  filter_upwards [aperture R simple pace,(RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j win warm k l L jk width w wp
  let m:=Fintype.card I
  let f:=k+1
  let x:=H f
  have rise:H j≤x:=WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jk
  have xp:1≤x:=warm.trans rise
  have head:25+24*((A).params j).columns≤49*x^2:=by
    have ch:=win.trans (pow_le_pow_left₀ (le_trans zero_le_one warm) rise 2)
    nlinarith only [ch,pow_le_pow_left₀ zero_le_one xp 2]
  have each(t:(Marks I).Mode):
      Poly.toll w t*WilsonSeparatedPrefixCanonicalHeard.roof R w t k j l ≤
      (49*4*4^m*((m:ℝ)^m))*x^(6+(4+6*L)*m+6*(f-j)*m):=by
    have tw:0<Poly.toll w t:=Poly.worth wp _
    have card:t.val.card≤ m:=Finset.card_le_univ _
    have dist:6*(k+1-(j+2))*t.val.card≤6*(f-j)*m:=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by dsimp [f];omega)) card
    have inside:x^(4+6*l)≤x^(4+6*L):=pow_le_pow_right₀ xp (by omega)
    have rest:x^(6*(k+1-(j+2))*t.val.card)≤x^(6*(f-j)*m):=pow_le_pow_right₀ xp dist
    have pack:((m:ℝ)*x^(4+6*l))^m≤((m:ℝ)*x^(4+6*L))^m:=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one xp) _))
        (mul_le_mul_of_nonneg_left inside (Nat.cast_nonneg _)) _
    have land:(H j)^4≤x^4:=pow_le_pow_left₀ (le_trans zero_le_one warm) rise _
    calc
      _ = (25+24*((A).params j).columns)*(H j)^4*4*4^m*
          (((m:ℝ)*x^(4+6*l))^m)*x^(6*(k+1-(j+2))*t.val.card):=by
        unfold WilsonSeparatedPrefixCanonicalHeard.roof
        simp only [Fintype.card_prod,Fintype.card_unit,one_mul]
        dsimp [x,f,m]
        field_simp [tw.ne']
      _ ≤ (49*x^2)*x^4*4*4^m*(((m:ℝ)*x^(4+6*L))^m)*x^(6*(f-j)*m):=by
        gcongr
      _ = _:=by simp only [pow_add,pow_mul,mul_pow];ring
  refine (sum_le_sum (fun t _=>each t)).trans_eq ?_
  simp only [sum_const,card_univ,nsmul_eq_mul]
  unfold front
  exact (mul_assoc ..).symm

end YM.Integration.WilsonSeparatedPrefixCanonicalRoof
