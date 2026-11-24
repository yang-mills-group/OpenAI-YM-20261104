import YM.Integration.WilsonCoherentMayerFuelWick
import YM.Integration.WilsonPositionSeparatedProfileMayerStencilPrice

/-! The polynomial arising from the genuine quadratic row has exactly the
original pre-aperture ledger price, including its dependence on walk length. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelTariff
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series


open WilsonCoherentMayerFuelPolynomial
variable (X:Coat T F)

def charge (q:Ledger f 2):ℝ := (1/2:ℝ)*∑ a:G.ColorIndex,∑ b:G.ColorIndex,|combo q.2.1 q.2.2 (X.finale q.1) a b|

theorem counted (q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks):
    Rise.coin (WilsonCoherentMayerFuelPolynomial.quadratic X q first last)≤charge X q := by
  unfold WilsonCoherentMayerFuelPolynomial.quadratic charge
  apply (Rise.funds 0 (zero_le_one (α:=ℝ)) _ _).trans
  simp only [Rise.pay_C,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by norm_num:(0:ℝ)≤1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Rise.collect 0 (zero_le_one (α:=ℝ)) _ _).trans
  apply Finset.sum_le_sum;intro a _
  apply (Rise.funds 0 (zero_le_one (α:=ℝ)) _ _).trans
  simp only [coordinate,Rise.pay_X,one_pow,one_mul]
  apply (Rise.collect 0 (zero_le_one (α:=ℝ)) _ _).trans
  apply Finset.sum_le_sum;intro b _
  apply (Rise.funds 0 (zero_le_one (α:=ℝ)) _ _).trans
  simp

private theorem entries {η r Q Y:ℝ} (θ : Rotator P L η r Q Y X) (n : ℕ) (i : Bond f) (p : Itinerary f (n+2)) :
    let M := Q*distPay η r Q (tubularPrice G L) X.B
    let R := (Fintype.card G.ColorIndex:ℝ)
    ∀ x y, |combo i p (X.finale n) x y| ≤ R^(n+2)*(Q*M^(n+1)) := by
  intro M R x y
  have hB := θ.scale
  have hg := hB.disc
  have hh := hB.heap X.B
  have hQ : 0≤Q := hB.fuel.le
  have hn : 0≤M := mul_nonneg hQ (mul_nonneg hg hh)
  let l (n i : ℕ) := if i ≤ n then M else Q
  have hu k (hk : k<n+2) : 0≤l n k := by unfold l; split <;> assumption
  have hs k j i : |X.finale n k j i| ≤ l n k := by
    unfold finale l; split
    next he => exact only_price ((spent_neg (hB.flank _)).1) θ.full.prices.le j i
    next he => exact only_price hB.price hB.eta.le j i
  have hZ (n : ℕ) : tally (n:=n+2) (l n) = Q*M^(n+1) := by
    induction n with
    | zero =>
      rw [count_mul 1,count_mul 0]
      change l 0 0*(l 0 1*1)=_; simp [l,mul_comm]
    | succ i hi =>
      rw [count_mul (i+2),show (fun t => l (i+1) (t+1))=l i from funext fun t => by simp [l], hi]
      unfold l; rw [if_pos (Nat.zero_le _),pow_succ]; ring
  rw [← hZ n]; exact pricingEntries S (X.finale n) (l n) i p (fun k _ => hs k) hu x y

theorem acquired {η r Q Y:ℝ} (θ:Rotator P L η r Q Y X) (q:Ledger f 2):
    charge X q ≤ Coat.capQ S η r Q (tubularPrice G L) X.B G 1 q := by
  rcases q with ⟨n,i,p⟩
  let R:ℝ:=Fintype.card G.ColorIndex
  let M:=Q*distPay η r Q (tubularPrice G L) X.B
  by_cases possible:Armed S (3*X.B) i p
  · have h:∀ a b,|combo i p (X.finale n) a b|≤R^(n+2)*(Q*M^(n+1)):= entries X θ n i p
    have total:(∑ a:G.ColorIndex,∑ b:G.ColorIndex,|combo i p (X.finale n) a b|) ≤
        ∑ _a:G.ColorIndex,∑ _b:G.ColorIndex,R^(n+2)*(Q*M^(n+1)):=
      Finset.sum_le_sum fun a _=>Finset.sum_le_sum fun b _=>h a b
    apply (mul_le_mul_of_nonneg_left total (by norm_num:(0:ℝ)≤1/2)).trans_eq
    simp only [Coat.capQ,cap,if_pos possible,Coat.centreQ,etaS,flagP,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,one_pow,mul_one]
    dsimp only [R,M]
    rw [mul_pow]
    ring
  · have vanish:combo i p (X.finale n)=0:=by
      refine filtered S (3*X.B) _ _ possible (X.finale n) ?_
      intro j _
      unfold Coat.finale;split
      next =>exact opposite _ (effects _ _ (X.span θ.room) (le_trans (by norm_num) θ.room.sight.1))
      next =>exact fun a b h=>X.span θ.room a b (by omega)
    simp [charge,Coat.capQ,cap,possible,vanish]

theorem repeated {η r Q Y:ℝ} (θ:Rotator P L η r Q Y X) (q:Ledger f 2)
    (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks) (k:ℕ) (B:Normal.poly (Eye X)):
    Rise.coin (WilsonCoherentMayerFuelWick.word X q first last k B) ≤
      ((Coat.capQ S η r Q (tubularPrice G L) X.B G 1 q)^k/k.factorial) * Rise.coin B := by
  unfold WilsonCoherentMayerFuelWick.word
  have pos (A:Normal.poly (Eye X)):0≤Rise.coin A:=by rw [Rise.metal];positivity
  have hq: Rise.coin (WilsonCoherentMayerFuelPolynomial.quadratic X q first last)≤Coat.capQ S η r Q (tubularPrice G L) X.B G 1 q :=
    (counted X q first last).trans (acquired X θ q)
  apply (Rise.funds 0 (zero_le_one (α:=ℝ)) _ _).trans
  apply mul_le_mul_of_nonneg_right _ (pos B)
  apply (Rise.funds 0 (zero_le_one (α:=ℝ)) _ _).trans
  simp only [Rise.pay_C,norm_inv,Complex.norm_real,Real.norm_natCast]
  rw [div_eq_mul_inv, mul_comm (↑k.factorial:ℝ)⁻¹]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (Rise.iterated 0 (zero_le_one (α:=ℝ)) _ _).trans
  exact pow_le_pow_left₀ (pos _) hq k

end YM.Integration.WilsonCoherentMayerFuelTariff
