import YM.Integration.WilsonAddressedPublicGuardClock
import YM.Integration.WilsonOriginalAlternativeTrialCapital
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicGuardCapital
open Lattice OPE Trace.Pilot Filter Real PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address OPE.Therm
open WilsonInvariantActionPosition Wilson RG Source Extra.Histories QuadraticLocal.Advent
open scoped Topology
variable {G:Gauge} (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta


open WilsonOriginalAlternativeTrialWallet WilsonAddressedPublicGuardFare
variable {V:Type}[Fintype V](d:V→ℕ)

include simple slow in
/-- On the chosen optical date the actual guarded row earns a radius on its own
    site. All radii use the same cutoff, the complete finite family, and the
    literal already-fitted vectors. -/
theorem original (forecast:WilsonReportLampForecast.Ready R.family.path.levels)
    (t:ℕ){δ:ℝ}(pd:0<δ):
    ∀ᶠ f:ℕ in atTop,let K:=berth R t f
    ∀ (N p:ℕ)(_live:K ≤ N)(_ref:∀v,R.family.ref (d v) ≤ K),
      (R.family.path.levels.params K).supportExponent=100 →
    ∀ (o:V→Site (R.family.side K p))(j:V→ℕ)(w:(i:V)→R.family.label (d i))
      (χ h z:V→ℝ)(η:ℝ),0 ≤ η→(∀i,a_ (j i) ≤ z i) →
      (∀i,(R.family.labels.level (d i)).coeffSize (word R (d i) K (χ i) (w i))  ≤ 
        h i*(a_ (j i)/a_ K)^((d i:ℝ)+η)) →
    ∀τ:ℝ,0<τ→∀i,
    (radius R d N p K o (fun l=>word R (d l) K (χ l) (w l)) (100+1+1) τ i)⁻¹  ≤ 
      (((Fintype.card V:ℝ)+1)*(1+(WilsonAddressedPublicGuardClock.ceiling G t δ*H_ f)^6*
        (h i*(z i/a_ f)^((d i:ℝ)+η)*(H_ f)^(((t:ℝ)+δ)*((d i:ℝ)+η)))))/τ:=by
  classical
  obtain ⟨start,salary⟩:=eventually_atTop.mp (WilsonOriginalAlternativeTrialCapital.original R d simple slow forecast)
  filter_upwards [eventually_ge_atTop start,WilsonAddressedCollarWindow.original R simple slow t pd,
      WilsonAddressedPublicGuardClock.thermal R simple slow t pd] with f due terms thermal
  let K:=berth R t f
  dsimp only
  intro N p live ref exactCap o j w χ h z η ep seats main τ hp i
  let v:=(fun l=>word R (d l) K (χ l) (w l))
  have original:=salary K (due.trans terms.1.le) N p live ref exactCap o v τ hp i
  have small:0 ≤ (R.family.labels.level (d i)).coeffSize (v i):=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have wage:0 ≤ h i:=nonneg_of_mul_nonneg_left (small.trans (main i))
    (Real.rpow_pos_of_pos (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) _)
  have rank:=WilsonAddressedPublicOpticalFare.quoted R (s:=(d i:ℝ)+η) (b:=h i) (zero_lt_one.trans (R.family.path.levels.fits.delayed f))
    (add_nonneg (Nat.cast_nonneg _) ep) wage terms.2.2 (seats i)
  have top:=pow_le_pow_left₀ (zero_lt_one.trans (R.family.path.levels.fits.delayed K)).le thermal 6
  have pos:=((zero_lt_one.trans (R.family.path.levels.fits.delayed K)).le.trans thermal)
  have joined:=mul_le_mul top ((main i).trans rank) small (pow_nonneg pos _)
  exact original.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add_right joined 1) (by positivity)) hp.le)

end YM.Integration.WilsonAddressedPublicGuardCapital
end
