import YM.Integration.WilsonMaxwellThermometerPublicHearing
import YM.Integration.WilsonPositionOriginalDiagnosticRegulator

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicFiling
open Filter Lattice Wilson RG Maxwell Maxwell.Free RG17 XSpace XSpace.Normalize
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicPocket
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→PhysMS.tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)
  (Y:Ultrafilter (ℕ×ℕ)) (simple:G.Simple) (B:ℕ)
  {I:Type} [Fintype I] (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)) (e:I→RG17.Free R.family 4)
local notation "L" => trail.curry (Y:Filter (ℕ×ℕ))
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)
local notation "v" => coordinates R F J V D
local notation "s" => WilsonMaxwellThermometerPublicPocket.measured R F J V K A


open XSpace.Normalize.Fray FVA2 FVA2.Arrival MS MS.Land MS.Local.Physical MS.Menus MS.Theater
open WilsonPositionPrescribedFormalTest
variable (U:Deck G) {H:(Bel R.family.book).Hierarchy} (prior:(Y:Filter _)≤f.fuse)
    (book:WilsonPositionCapTransport.Book (f:=f) (l:=Y) (H:=H) A J) (lead:Leading F J)

theorem band (r:ℝ) (N p:ℕ)
    (hn:WilsonMeasuredWindow.stop R.family.path.levels simple B r≤N):
    let m:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
    let h:=(Real.sqrt (R.family.path.levels.clock.hatBeta m))⁻¹
    |g r (N,p)|≤2*h ∧ h≤2*|g r (N,p)|:=by
  let m:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
  let x:=R.family.path.levels.clock.hatBeta m
  let y:=R.family.path.β N p m
  have roster: x/2≤y ∧ y≤2*x :=(R.makes.wilson.represents N p m hn).band
  have hx:0<x:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have hy:0<y:=lt_of_lt_of_le (half_pos hx) roster.1
  have X:0<Real.sqrt x:=Real.sqrt_pos.mpr hx
  have Y₀:0<Real.sqrt y:=Real.sqrt_pos.mpr hy
  have a:Real.sqrt x≤2*Real.sqrt y:=by
    have z:=Real.sqrt_le_sqrt (show x≤4*y by linarith [roster.1])
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at z
  have b:Real.sqrt y≤2*Real.sqrt x:=by
    have z:=Real.sqrt_le_sqrt (show y≤4*x by linarith [roster.2])
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at z
  change |(Real.sqrt y)⁻¹|≤2*(Real.sqrt x)⁻¹ ∧ (Real.sqrt x)⁻¹≤2*|(Real.sqrt y)⁻¹|
  rw [abs_of_pos (inv_pos.mpr Y₀)]
  simpa only [one_div,div_eq_mul_inv,one_mul] using
    (show 1/Real.sqrt y≤2/Real.sqrt x ∧ 1/Real.sqrt x≤2/Real.sqrt y from
      ⟨(div_le_div_iff₀ Y₀ X).mpr (by linarith),
       (div_le_div_iff₀ X Y₀).mpr (by linarith)⟩)

local notation "tally" => WilsonPositionOriginalDiagnosticRegulator.price A (d:=6) le_rfl U V (reference G 6)

include prior book lead in
theorem transfer (C:ℝ) (hc:0<C)
    (paid:∀ᶠw:ℝ×(ℕ×ℕ) in L,tally w.1 w.2≤C*|g w.1 w.2|):
    ∀ᶠw:ℝ×(ℕ×ℕ) in L,WilsonPositionOriginalCalibrationSensitivity.price F J V 6 w.1 ≤ (4*C)*|g w.1 w.2|:=by
  apply eventually_curry_iff.mpr
  filter_upwards [eventually_curry_iff.mp paid,
    WilsonPositionOriginalDiagnosticRegulator.received A (d:=6) le_rfl U V F J lead prior simple book]
      with r one earn
  let m:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
  let h:=(Real.sqrt (R.family.path.levels.clock.hatBeta m))⁻¹
  have actual:∀ᶠ z:ℕ×ℕ in (Y:Filter _), |g r z| ≤ 2*h ∧ h ≤ 2*|g r z|:=by
    filter_upwards [(Next.UVStress.large_mesh f m).filter_mono prior] with z deep
    exact band R simple B r z.1 z.2 deep
  have uniform:∀ᶠ z:ℕ×ℕ in (Y:Filter _),tally r z≤C*(2*h):=by
    filter_upwards [one,actual] with z observed coin
    exact observed.trans (mul_le_mul_of_nonneg_left coin.1 hc.le)
  have cost:=WilsonPositionOriginalDiagnosticPurse.fee U V (WilsonPositionPrescribedScreen.hierarchy F J 6 r) (reference G 6)
  have fixed:WilsonPositionOriginalCalibrationSensitivity.price F J V 6 r ≤ C*(2*h):=
    cost.trans (le_of_tendsto (earn _) uniform)
  filter_upwards [actual] with z coin
  exact fixed.trans (by nlinarith [mul_le_mul_of_nonneg_left coin.2 hc.le])

include prior book lead in
/-- The only accuracy test here is on the original finite regulatory survey
with its actual numerical coupling and on the very same signed course. -/
theorem original (C:ℝ) (hc:0<C)
    (paid:∀ᶠw:ℝ×(ℕ×ℕ) in L,tally w.1 w.2≤C*|g w.1 w.2|):
    ∀ε>0,∀ᶠw:ℝ×(ℕ×ℕ) in L,‖WilsonMaxwellThermometerPublicReturn.bill R F J V K A D e w.1 w.2‖≤ε*|g w.1 w.2|:=
  WilsonMaxwellThermometerPublicHearing.original R F J V K A Y simple B D e prior book lead (4*C)
    (by positivity) (transfer R F J V A Y simple B U prior book lead C hc paid)

end YM.Integration.WilsonMaxwellThermometerPublicFiling
