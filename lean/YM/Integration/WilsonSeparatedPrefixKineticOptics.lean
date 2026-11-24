import YM.Integration.WilsonSeparatedPrefixKineticGeometry
import YM.Integration.WilsonSeparatedPrefixKineticLedger
import YM.Integration.WilsonSeparatedPrefixKineticCash

/-! The accumulated finite-cover kinetic chart at the original physical scale.
The opening and all numerical prices precede the two regulators. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixKineticOptics
open Filter Finset Function Lattice Wilson RG RG.Supply Precision PowerSeries
open AllOrder AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics ConnectedActivityE6
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonReportingAbsoluteInletForecastBooks
open WilsonOlderFreshSoftSocketKinetic WilsonSeparatedPrefixKineticForecast WilsonSeparatedPrefixKineticMarket
open WilsonSeparatedPrefixKineticGeometry WilsonSeparatedPrefixKineticTruncation WilsonSeparatedPrefixKineticEdge
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "V" => R.family.path.levels
local notation "g" => regulatorRun R.family

private lemma down {n e:ℕ}(ne:n ≤ e)(B:Cost):mass n B ≤ mass e B:=by
  unfold mass;exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _=>abs_nonneg _)

include simple in
theorem window (seller:ℕ→Gear G→ℝ)(sources:FundedMarkedCoverRows.prices seller R.kit)
    (n k A:ℕ)(order:n ≤ Burn.horizon k+2):∀ᶠ b:ℕ in atTop,∀K N per,b ≤ K→K ≤ N→span R A b K→
    (∀i,b ≤ i→i<K→|(R.T.history N per i).beta-thermal R k N per i| ≤ (g N per i)^n)→
    |g N per K-g N per b*value n (kinetic V R.metals.O N K b) (g N per b)| ≤ (g N per b)^(n+1):=by
  let e:=Burn.horizon k+2
  obtain ⟨B,B1,geometry⟩:=corridor R simple A
  obtain ⟨C,windowFee⟩:=WilsonSeparatedPrefixKineticMarket.original R simple seller sources e
  obtain ⟨S,sale⟩:=WilsonSeparatedPrefixKineticCash.shelf n e C B1
  filter_upwards [geometry,windowFee,spend R simple S.x S.d] with b geo wages pay K N per bK KN admitted evidence
  obtain ⟨⟨z1,a1,aCap,days⟩,clock⟩:=geo K N per bK KN admitted
  let M:=(e+2:ℝ)*C.buy (aperture R b K)
  obtain ⟨M1,small,whole⟩:=sale _ _ _ z1 a1 aCap (Nat.cast_nonneg (K-b)) days
  let w:=g N per b
  have w0:0<w:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (bK.trans KN)))
  have funds:S.buy (wage R b) ≤ w⁻¹:=pay N per (bK.trans KN)
  have reserve:4*M ≤ w⁻¹:=small.trans funds
  have co:(4*M)*w ≤ 1:=(mul_le_mul_of_nonneg_right reserve w0.le).trans_eq (inv_mul_cancel₀ w0.ne')
  have m0:0 ≤ M:=zero_le_one.trans M1
  have w1:2*w ≤ 1:=by nlinarith only [co,mul_nonneg (sub_nonneg.mpr M1) w0.le,w0.le]
  have narrow:(2*w)*M ≤ 1/2:=by nlinarith only [co]
  have ratio (i:ℕ)(bi:b ≤ i)(iK:i ≤ K):3/4*w ≤ g N per i ∧ g N per i ≤ 5/4*w:=by
    have h:=clock i bi iK;exact ⟨(le_div_iff₀ w0).mp h.1,(div_le_iff₀ w0).mp h.2⟩
  obtain ⟨km,steps⟩:=wages N K bK KN
  have foot:=WilsonSeparatedPrefixKineticLedger.trail R simple bK KN order M1 w1 narrow
    (fun i bi iK=>by linarith only [(ratio i bi iK).2,w0.le]) (fun i bi iK=>by
      have xpos:0<g N per (i+1):=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (iK.trans_le KN)))
      apply (div_le_iff₀ xpos).mpr
      linarith only [(ratio i bi iK.le).2,(ratio (i+1) (by omega) iK).1,w0.le])
    (fun i bi iK=>(down order _).trans (km i bi iK)) (fun i bi iK=>by
      obtain ⟨f,h⟩:=steps i bi iK;exact ⟨(down order _).trans f,(down order _).trans h,h⟩) evidence
  refine foot.trans ((mul_le_mul_of_nonneg_left (WilsonSeparatedPrefixKineticCash.quote n M1 (by positivity:0 ≤ 2*w) w1) (Nat.cast_nonneg (K-b))).trans ?_)
  calc
    _=((K-b:ℕ)*(2:ℝ)^(n+2)*WilsonSeparatedPrefixKineticCash.fee n*M^(n+4))*w^(n+2):=by rw [mul_pow];ring
    _ ≤ w⁻¹*w^(n+2):=mul_le_mul_of_nonneg_right (whole.trans funds) (pow_nonneg w0.le _)
    _=_:=by change w⁻¹*w^(n+2)=w^(n+1);rw [pow_succ w (n+1)];field_simp

end YM.Integration.WilsonSeparatedPrefixKineticOptics
end
