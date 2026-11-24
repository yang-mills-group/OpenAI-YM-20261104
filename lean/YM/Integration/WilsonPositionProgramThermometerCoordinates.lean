import YM.Integration.WilsonPositionProgramSubmittedCoordinates
import YM.Integration.WilsonPositionProgramReportedField
import YM.Integration.WilsonOriginalThermometerPalette

/-! The (6,4,4) incoming numerical values and their finite regulator-independent
income, including the entire measured lower-sector re-expression. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramThermometerCoordinates
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price
open WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Embroider Source Source.Drops WilsonCoeffUV.Mer
open WilsonPositionProgramReportedField WilsonPositionProgramSubmittedCoordinates
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}

def upper (A:Group R.family 6)(k N p:ℕ)(i:Fin 3):R.family.label (levels i):=
  entire R (levels i) k (N,p) (coordinates R A k N p i)

def issued (D:Fin 3→ℕ)(fit:∀i,levels i<D i)(A:Group R.family 6)(k N p:ℕ)
    (phase:Fin 3→ℂ →L[ℝ] ℝ):Herit (deck (G:=G) levels D fit):=
  submitted R levels D fit (upper R A k N p) phase

def price (e:ℕ)(i:Fin 3):ℝ:=
  Fintype.card (Alma (R.family.labels.level (levels i))) * (e+1:ℕ) *
    (2:ℝ)^(univ.sup fun j:(R.family.labels.level (levels i)).Index=>((R.family.labels.level (levels i)).grades j).2)

theorem same (D:Fin 3→ℕ)(fit:∀i,levels i<D i)(A:Group R.family 6)(k N p:ℕ)
    (phase:Fin 3→ℂ →L[ℝ] ℝ)(i:Fin 3)(v:(R.family.labels.level (levels i)).Index):
    (issued R D fit A k N p phase i) (plain (R.family.labels.level (levels i)) v) =
      PowerSeries.C (phase i ((upper R A k N p i) v)) :=
  entry R levels D fit (upper R A k N p) phase i v

theorem original (simple:G.Simple)(δ:ℝ)(pos:0<δ)(e:ℕ)(D:Fin 3→ℕ)(fit:∀i,levels i<D i):
    ∀ᶠ k:ℕ in atTop,∀A:Group R.family 6,A.station.k=k → A.station.checked f H A.horizon →
    ∀N p:ℕ,k<N → ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(i:Fin 3),
    fee (issued R D fit A k N p phase) e i ≤
      price R e i*‖phase i‖*((R.family.path.levels.clock.hatBeta k)^δ*salary R A) := by
  filter_upwards [WilsonOriginalThermometerPalette.station (f:=f) (H:=H) R simple δ pos] with k sold
  intro A date checked N p top phase i
  let F:=R.family.labels.level (levels i)
  let bump:ℝ:=2^(univ.sup fun v:F.Index=>(F.grades v).2)
  let card:ℝ:=Fintype.card (Alma F)*(e+1:ℕ)
  let income:ℝ:=(R.family.path.levels.clock.hatBeta k)^δ*salary R A
  have issued₀:F.coeffSize (upper R A k N p i) ≤ bump*income:=
    (WilsonPositionProgramReportedField.purchased R (levels i) k (N,p) top.le (coordinates R A k N p i)).trans
      (mul_le_mul_of_nonneg_left (sold A date checked N p top i) (by positivity))
  calc
    _ ≤ card*(‖phase i‖*F.coeffSize (upper R A k N p i)) :=
      WilsonPositionProgramSubmittedCoordinates.paid R levels D fit (upper R A k N p) phase e i
    _ ≤ card*(‖phase i‖*(bump*income)):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left issued₀ (norm_nonneg _)) (by positivity)
    _ = _ :=by change _=card*bump*‖phase i‖*income; ring

end YM.Integration.WilsonPositionProgramThermometerCoordinates
end
