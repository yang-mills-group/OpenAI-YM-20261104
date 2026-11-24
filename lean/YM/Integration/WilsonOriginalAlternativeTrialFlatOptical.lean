import YM.Integration.WilsonOriginalTwoFlatWithdrawal
import YM.Integration.WilsonOriginalOccupiedOpticalRate

/-! After capture, the occupied contribution at either original flat has any purchased coupling power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialFlatOptical
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open private YM.Push.Local.gasRate_le from YM.Push.LOCAL_SPLITTING.Delay
include simple in
theorem original (n d a p:ℕ) (np:0<n) (load:∀s:marks.Mode,s.val.card ≤ n)
    (C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀ᶠ f:ℕ in atTop,∀ (N per m k b reserve:ℕ) (_top:f+1 ≤ N) (bt:b<f+1),start ≤ b →
    ((f+1-b+reserve:ℕ):ℝ) ≤ C*(1+Real.log (H (f+1)))^d →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(X I:Type) [Countable I] [Nonempty X] (o:V → Site (R.family.side (f+1) per))
    (A:Gallery X I o (Ψ (f+1)) marks) (w:V → ℝ), (∀v,0<w v) →
    A.E.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent 1 →
    A.K.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent (κ (f+1)) →
    ∀(x:X)(s:marks.Mode)(u i:ℕ),(mu:m ≤ u) → (ui:u ≤ i) → (ib:i ≤ b) → WilsonSingleHardRadius.first R simple ≤ u →
    ∀(Z:Support (R.family.side b per))(center:Site (R.family.side b per)),center∈Z →
    (∀a∈s.val,sites R o bt.le a∈Z) →
    let fee:=Poly.toll (wallet R w bt.le) s
    let roof:=(shards marks s).card+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*(κ b)
    let gain:=(H (f+1))^a*(Real.exp (n*(reserve:ℝ)*(scale (H (f+1)))^3)*Poly.toll w s)
    let value:=‖(((Ψ i).eval 1:ℂ)⁻¹)*((gust R.family.path N per (f+1) (A.density x) i (ib.trans bt.le) 1).part s-
      (gust R.family.path N per (f+1) (fun U=>((Ψ (f+1)).eval U:ℂ) • Poly.pass (A.E.log x U)) i (ib.trans bt.le) 1).part s)‖
    let budget:=(e*(regulatorRun R.family N per (f+1))^p)*roof
    gain*value ≤ budget ∧ (1 ≤ gain → value ≤ budget):=by
  obtain ⟨start,season⟩:=eventually_atTop.mp (R.family.path.levels.fits.deep.eventually_ge_atTop n)
  refine ⟨max start (WilsonCenteredCaptureClock.first R simple),?_⟩
  filter_upwards [WilsonOriginalOccupiedOpticalRate.original R simple n d a p C cp e ep] with
    f rates N per m k b reserve top bt sb span way D Q π Γ Ψ course ticket X I hc hx o A w wp reg hard x s u i mu ui ib fixed Z center home homes
  let g:=regulatorRun R.family N per (f+1)
  let z:=scale (H (f+1))
  let l:=f+1-b
  let E:=Real.exp (n*(l:ℝ)*z^3)
  let B:=Real.exp (n*(reserve:ℝ)*z^3)
  let fee:=Poly.toll (wallet R w bt.le) s
  let val:=‖(((Ψ i).eval 1:ℂ)⁻¹)*((gust R.family.path N per (f+1) (A.density x) i (ib.trans bt.le) 1).part s-
    (gust R.family.path N per (f+1) (fun U=>((Ψ (f+1)).eval U:ℂ) • Poly.pass (A.E.log x U)) i (ib.trans bt.le) 1).part s)‖
  have val0:0 ≤ val:=norm_nonneg _
  have hp:0 ≤ H (f+1):=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have z0:0 ≤ z:=by dsimp [z,scale];linarith only [le_max_left 0 (Real.log (Real.log (H (f+1))))]
  have r0:0 ≤ fee:=(Poly.worth (positive R w wp bt.le) s).le
  let roof:=((shards marks s).card:ℝ)+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
    R.alloy.B.a.clock.hatBeta b*(κ b)
  have ever:∀j,b ≤ j → κ j ≤ 1:=fun j _=>Real.sqrt_le_one.mpr (YM.Push.Local.gasRate_le _)
  obtain ⟨tiny,rate⟩:=rates N per top (l+reserve) span
  have charge:=WilsonOriginalTwoFlatWithdrawal.original R way D Q π Γ Ψ course ticket o A w wp simple mu
    (ui.trans ib) fixed ((le_max_right ..).trans sb) ui ib bt top Z center home
    (fun j bj=>season j (((le_max_left ..).trans sb).trans bj)) load ever s homes n np (load s) tiny reg hard x
  have costs:=WilsonOriginalOccupiedClock.restored R simple bt.le (f:=f) le_rfl w wp s
  have meter:Real.exp (s.val.card*(l:ℝ)*z^3) ≤ E:=by
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast load s) (Nat.cast_nonneg l)) (pow_nonneg z0 _)
  have earlier:Poly.toll w s ≤ E*fee:=costs.trans (mul_le_mul_of_nonneg_right meter r0)
  let bill:=(WilsonOriginalOccupiedWallet.inverseAmplitude n (κ (f+1))*price n)
  change fee*val ≤ bill*roof at charge
  have factor:Real.exp (n*((l+reserve:ℕ):ℝ)*z^3)=B*E:=by
    rw [Nat.cast_add]
    dsimp only [B,E]
    rw [←Real.exp_add]
    congr 1
    ring
  change (H (f+1))^a*Real.exp (n*((l+reserve:ℕ):ℝ)*z^3)*bill ≤ e*g^p at rate
  rw [factor] at rate
  have reserveCost:B*Poly.toll w s ≤ (B*E)*fee:=by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left earlier (Real.exp_pos _).le
  let gain:=(H (f+1))^a*(Real.exp (n*(reserve:ℝ)*(scale (H (f+1)))^3)*Poly.toll w s)
  have bounded:gain*val ≤ (e*g^p)*roof:=by
    calc gain*val ≤ ((H (f+1))^a*((B*E)*fee))*val:=mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left reserveCost (pow_nonneg hp _)) val0
         _=((H (f+1))^a*(B*E))*(fee*val):=by ring
         _ ≤ ((H (f+1))^a*(B*E))*(bill*roof):=
           mul_le_mul_of_nonneg_left charge (mul_nonneg (pow_nonneg hp _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
         _=((H (f+1))^a*(B*E)*bill)*roof:=by ring
         _ ≤ _:=mul_le_mul_of_nonneg_right rate (by
           dsimp only [roof,WilsonOriginalFlatOccupiedRate.bill,WilsonOriginalFlatOccupiedRate.roof]
           have bp:0 ≤ R.alloy.B.a.clock.hatBeta b:=zero_le_one.trans (R.family.path.levels.fits.delayed b).le
           have kp:0 ≤ κ b:=(Real.sqrt_nonneg _)
           positivity)
  exact ⟨bounded,fun h=>(le_mul_of_one_le_left val0 h).trans bounded⟩

end YM.Integration.WilsonOriginalAlternativeTrialFlatOptical
