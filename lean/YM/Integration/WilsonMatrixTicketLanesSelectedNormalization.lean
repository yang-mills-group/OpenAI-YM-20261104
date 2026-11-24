import YM.Integration.WilsonMatrixTicketLanesSelectedInput

/-! The original field and packet normalization at the prescribed reporting
clock. All finer cutoffs use this same scale of the independent coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesSelectedNormalization
open Function Filter Finset Lattice Wilson RG Source Marker Precision
open PhysicalNext.Repeat.Legato LocalComparison RG3.Script.Picnic FullQLocal.RenderedStep IterationFour.Vacuum
open ActualOriginalQReaders ActualOriginalQCharges
open private capped from YM.Integration.WilsonReportingPrescribedOldScale
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical BigOperators
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (Q:MS.Land.Prescription B)
local notation "base" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)

def stamp (μ:ℝ) (d:LocalFormal.Datum R.family (Stock.census V)):ℝ:=
  μ+R.family.S.scale d.cutoff-R.family.S.scale (d.level+1)

theorem clock (μ:ℝ) (d:LocalFormal.Datum R.family (Stock.census V)):
    stamp R μ d-R.family.S.scale d.cutoff=μ-R.family.S.scale (d.level+1):=by
  unfold stamp
  ring

theorem purchased (μ:ℝ) (K:ℕ):
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀(d:LocalFormal.Datum R.family (Stock.census V))
      (o:V→Site (R.family.side (d.level+1) d.period))(r:V→ℕ), (∀i,r i≤K)→
      ActualOriginalQInitialInput.normalizer R simple u J A d Q o (stamp R μ d) r≤
        C*(R.family.path.levels.clock.hatBeta (d.level+1))^e:=by
  obtain ⟨c,cp,e,fees⟩:=ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  obtain ⟨a,ap,dates⟩:=date R simple
  let W:=max 1 (totalRowPrice (base) u (fun _=>1) 1)
  let D:=max 1 c*(max 1 a)^e
  have wp:1≤W:=le_max_left _ _
  have dp:1≤D:=one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (le_max_left _ _))
  refine ⟨D*W,mul_pos (zero_lt_one.trans_le dp) (zero_lt_one.trans_le wp),e,?_⟩
  intro d o orders upper
  let β:=R.family.path.levels.clock.hatBeta (d.level+1)
  have bp:1≤β:=(R.family.path.levels.fits.delayed _).le
  have paid:1≤D*β^e:=one_le_mul_of_one_le_of_one_le dp (one_le_pow₀ bp)
  have hold:1+‖R.family.S.scale (d.level+1)‖≤(max 1 a)*β:=
    (dates _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans bp))
  have charges(s:Slot u):‖fee Q u (stamp R μ d-R.family.S.scale d.cutoff) orders s‖≤D*β^e:=by
    rw [clock]
    calc
      _ ≤ c*(1+‖R.family.S.scale (d.level+1)‖)^e:=fees s.1 (orders s.1) (upper s.1) s.2 _
      _ ≤ max 1 c*((max 1 a)*β)^e:=mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by positivity) hold e)
        (by positivity) (zero_le_one.trans (le_max_left _ _))
      _ = _:=by unfold D;rw [mul_pow];ring
  exact (capped R simple u J A d Q o (stamp R μ d) orders paid charges).trans_eq (by dsimp only [W];ring)

end YM.Integration.WilsonMatrixTicketLanesSelectedNormalization
