import YM.Qlocal.Ramp
import YM.MSbar.Ballet.Visor
import YM.OPE.Therm.Request

/-! Buy the analytic vacuum and flag estimates in the same pre-launch
schedule used by the measured marked comparison. All thresholds precede
the choice of the physical history and the field readouts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Schedule
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

/-- The late-order growth condition in the vacuum invoice follows from
the actual field construction on every selected run. -/
def vacuumInvoice (u : G.ColorIndex) (V : MSbar.Heath.Voice G) : Goal G :=
  fun _ _ A F =>
    (Tendsto (fun m => (A.B.a.params m).order) atTop atTop → Estate u V A.B) ∧
      Mallow.Hoard F.shape A.delay ∧ OPE.Therm.Poetry A.B.a

theorem vacuumInvoice_obtainable (hG : G.Simple) (u : G.ColorIndex)
    (V : MSbar.Heath.Voice G) (clear : MSbar.Heath.Clear G V) :
    Obtainable (vacuumInvoice u V) := by
  intro s T C z R E hdr
  obtain ⟨p, hb⟩ := MSbar.Ballet.paymentP (G := G) (ThroughLaunch.bearing s T)
  refine ⟨p, ?_⟩
  intro l hl D w v Z F S pocket records admissible P menu wait
  let M := ThroughLaunch.currency s T l
  have prepared := fun i => hb i (D.L i) ((hl i).trans (D.large i).need)
  obtain ⟨W₁,h₁,H₁⟩ := MSbar.Alto.album hG P M.K M.O (fun i => (prepared i).pre) wait
  obtain ⟨W₂,h₂,H₂⟩ := MSbar.Ballet.stage M.O M.K u V W₁ hG (chart_ok G) prepared clear
  obtain ⟨W₃,h₃,H₃⟩ := Mallow.loft W₂
  obtain ⟨W₄,h₄,H₄⟩ := Mallow.stocking Z W₃
  obtain ⟨W₅,h₅,H₅⟩ := OPE.Therm.poetry_delay W₄
  refine ⟨W₅,h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))), ?_⟩
  intro Y hY cost bar W price B archive shape alloy exchange η q d b h j hf hv hw ha
  have dome := H₃.height Y (h₄.trans (h₅.trans hY)) bar W B.a B.valid
  exact ⟨fun growth => ⟨H₁ Y (h₂.trans (h₃.trans (h₄.trans (h₅.trans hY)))) bar W _ B.valid,
    H₂ Y (h₃.trans (h₄.trans (h₅.trans hY))) bar W _ B.valid, dome.1,dome.2,growth⟩,
    H₄ Y (h₅.trans hY), H₅ Y hY W B.a B.valid⟩

open FullVolume

/-- Consume the invoice on the literal selected orbit of R. -/
theorem docket_of_invoice (hG : G.Simple) (R : Run G) (u : G.ColorIndex)
    (V : MSbar.Heath.Voice G)
    (price : vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels := by
  have growth : Tendsto (fun m => (R.alloy.B.a.params m).order) atTop atTop := by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with m hm
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 m hm).1)
  have ch := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors
    R.makes R.carries R.books).1
  exact ⟨keeper R.b R.Q R.T R.t R.stories R.doors ch V hG price.2.1 u (price.1 growth),
    price.2.2⟩

/-- Add the same-trajectory vacuum docket and flag prices to any previously
obtainable marked campaign without fixing its tests, periods or horizons. -/
theorem run_with_vacuum {H : Goal G} (hG : G.Simple) (buy : Obtainable H)
    (d : ℝ) (hd : 0 < d) :
    ∃ (R : Run G) (u : G.ColorIndex),
      R.family.path.levels.clock.kernel.penalty = d ∧ H R.metals R.rolls R.alloy R.kit ∧
      Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧ OPE.Therm.Poetry R.family.path.levels := by
  haveI := hG.nontrivial_color
  have degree : 0 < G.lieDim := by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u : G.ColorIndex := ⟨0, degree⟩
  obtain ⟨V, clear⟩ := MSbar.Heath.vocals G
  obtain ⟨R, penalty, original, inv⟩ := Run.rampK hG (buy.also (vacuumInvoice_obtainable hG u V clear)) d hd
  exact ⟨R,u,penalty,original,docket_of_invoice hG R u V inv⟩

end YM.Qlocal.Schedule
