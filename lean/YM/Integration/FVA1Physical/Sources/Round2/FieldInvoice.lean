import YM.Integration.FVA1Physical.Sources.Round2.FieldLoad
import YM.Integration.FVA1Physical.Round2.VacuumInvoice

/-! Buy the analytic vacuum and flag estimates in the same pre-launch
schedule used by the measured marked comparison. All thresholds precede
the choice of the physical history and the field readouts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Qlocal.Schedule RGComparison.Core16.Spool YM.MSbar
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical
variable {G : Gauge}

variable {κ:Type} [Fintype κ]

/-- One entry on the same schedule fixes every aperture size and perturbative order
for the given finite template, including both real and imaginary components. -/
def fieldInvoice (u:G.ColorIndex) (V:MSbar.Heath.Voice G) (J:κ→Lamp G) : Goal G :=
  fun M _ A _ => AllFieldLoad M.K M.p.kernel M.O A.B.a u V J

theorem fieldInvoice_obtainable (hG:G.Simple) (u:G.ColorIndex) (V:MSbar.Heath.Voice G)
    (clear:MSbar.Heath.Clear G V) (J:κ→Lamp G) : Obtainable (fieldInvoice u V J) := by
  intro s T C z R E hdr
  obtain ⟨p,hb⟩:=MSbar.Ballet.paymentP (G:=G) (ThroughLaunch.bearing s T)
  refine ⟨p,?_⟩
  intro l hl D w v Z F S pocket records admissible P menu wait
  let M:=ThroughLaunch.currency s T l
  have prepared:=fun i=>hb i (D.L i) ((hl i).trans (D.large i).need)
  obtain ⟨buy,hprice,offers⟩:=all_field_stage M.O M.K u V J wait hG (chart_ok G) prepared clear
  refine ⟨buy,hprice,?_⟩
  intro Y hY cost bar W price B archive shape alloy exchange η q d b h j hf hv hw ha
  exact offers Y hY bar W B.a B.valid

end YM.Integration.FVA1Physical.Round2.Curvature
