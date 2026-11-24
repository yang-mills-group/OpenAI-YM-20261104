import YM.Integration.FVA1Physical.Round2.PhysicalFieldWords
import YM.Integration.FVA1Physical.Round2.FieldWordDegrees
import YM.Integration.FVA1Physical.Wilson.BankOrbit
import YM.Integration.FVA1Physical.Sources.Round2.ThermalConnected

/-! The physical chart derivatives, connected thermal readings and the
independent inherited Wilson coefficients use a single calibrated run. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk
open MSbar.Mosaic Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

theorem field_word_trajectory {goal:Goal G} (extra:Obtainable goal) (hG:G.Simple) (cost:ℝ) (pos:0<cost) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G) (cle:Clear G V),
      R.family.path.levels.clock.kernel.penalty=cost ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ PinnedFieldWords J R u ∧ PinnedEmissions J R u ∧
      ThermalConnectedReadings J R u ∧ iteratedBankInvoice u V cle hG R.metals R.rolls R.alloy R.kit := by
  haveI:=hG.nontrivial_color
  have dim:0<G.lieDim:=by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  let u:G.ColorIndex:=⟨0,dim⟩
  obtain ⟨V,cle⟩:=MSbar.Heath.vocals G
  let reader:=(selectedThreshold_obtainable (G:=G) (readingMenu J V cle hG)).also
    (fieldInvoice_obtainable hG u V cle J)
  let emitter:=mapThreshold_obtainable (G:=G) (emissionMenu J V cle hG)
  let marks:=maskFluctuationInvoice_obtainable J hG u V cle
  let bank:=bankInvoice_obtainable u V cle hG
  let purchases:=((extra.also fixedWilsonChart_obtainable).also (reader.also emitter)).also
    ((marks.also bank).also (vacuumInvoice_obtainable hG u V cle))
  obtain ⟨R,pen,⟨⟨⟨grant,frame⟩,⟨⟨read,field⟩,rows⟩⟩,⟨⟨masks,orbit⟩,invoice⟩⟩⟩:=Run.rampK hG purchases cost pos
  have point:=physical_field_pinned_on J hG R u V cle frame read field invoice
  have paid:=pinned_emissions J hG R u V cle frame rows invoice
  exact ⟨R,u,V,cle,pen,grant,frame,physical_field_words J hG R u point paid,paid,
    connected_from_thermal J hG R u (fluctuation_masks_pinned_on J hG R u V cle frame masks invoice),orbit⟩

/-- A seed at the physical insertion level. The orbit only accesses this
level of its boundary family, so no arbitrary continuation is required. -/
def fieldBoundary (R:PhysicalNext.Repeat.Legato.Run G) (n i:ℕ)
    (seed:Nesting G (R.family.path.levels.S.side i n)) (j:ℕ) : Nesting G (R.family.path.levels.S.side j n) :=
  if e:i=j then e ▸ seed else 0

theorem fieldBoundary_at (R:PhysicalNext.Repeat.Legato.Run G) (n i:ℕ)
    (seed:Nesting G (R.family.path.levels.S.side i n)) : fieldBoundary R n i seed i=seed := by
  simp [fieldBoundary]

end YM.Integration.FVA1Physical.Round2.Curvature
