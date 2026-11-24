import YM.Integration.FVA1Physical.Sources.Round2.FieldInvoice
import YM.Integration.FVA1Physical.Sources.Round2.FieldPalette
import YM.Integration.FVA1Physical.Sources.Round2.FieldProgram

/-! The conditional mixed field comparison on actual inherited scenes, with all
calibration, cutoff, source budgets and Gaussian projection inputs discharged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Qlocal.Schedule RGComparison.Core16.Spool YM.MSbar Push.Uniform
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

open YM.Integration.FVA1Physical.Wilson YM.Integration YM.MSbar.Heath
open Exterior Tree MSbar.Rolling MSbar.Midpoint MSbar.Whisk Pressure

/-- The normalized field comparison everywhere along the regular portion of the
chosen non-bare trajectory. The same forest and bits also determine the vacuum's outgoing jet. -/
def RealizedPorts (J:κ→Lamp G) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G) : Prop :=
      ∀ p s m L:ℕ, 6 ≤ s → 4 ≤ m → p+2 ≤ m →
      ∀ᶠ k:ℕ in atTop,∀ N n, k ≤ N →
        (∃ S:Scene R.family.path.levels n p,Realized R.alloy.B.kin N n k p (Lis.sun G u) S) ∧
        ∀ S:Scene R.family.path.levels n p,Realized R.alloy.B.kin N n k p (Lis.sun G u) S →
        ∀ j,k ≤ j → j < N → ∃ (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices),
          let A:= sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let x:=R.family.path.levels.clock.hatBeta j
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          S.Poly j = A.Zpost R.metals.O ∧
          ∀ (z:Site A.f) (Z:Positions (Primary A.c G)), ‖Z‖ ≤ Mosaic.hull x → ∀ part:Bool,
            FieldPort A R.metals.O V p L J part y (y^Mosaic.pawn p) z Z

def PinnedPorts (J:κ→Lamp G) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G) : Prop :=
      ∀ p s m L:ℕ, 6 ≤ s → 4 ≤ m → p+2 ≤ m →
      ∀ᶠ k:ℕ in atTop,∀ N n, k ≤ N →
        (∃ S:Scene R.family.path.levels n p,Realized R.alloy.B.kin N n k p (Lis.sun G u) S) ∧
        ∀ (S:Scene R.family.path.levels n p) (scene:Realized R.alloy.B.kin N n k p (Lis.sun G u) S),
        ∀ (j:ℕ) (kj:k ≤ j) (jN:j < N),
          let F:=(scene.step j jN kj).choose
          let v:=(scene.step j jN kj).choose_spec.choose
          let A:= sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let x:=R.family.path.levels.clock.hatBeta j
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          S.Poly j = A.Zpost R.metals.O ∧
          ∀ (z:Site A.f) (Z:Positions (Primary A.c G)), ‖Z‖ ≤ Mosaic.hull x → ∀ part:Bool,
            FieldPort A R.metals.O V p L J part y (y^Mosaic.pawn p) z Z

/-- Consume the prices on an already-selected construction and fixed chart voice.
Additional invoices may have been purchased before choosing this Run. -/
theorem actual_field_ports_pinned_on (J:κ→Lamp G) (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (fields:fieldInvoice u V J R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedPorts J R u V := by
  have docket:=(Qlocal.Schedule.docket_of_invoice hG R u V invoice).1
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  have estate:=invoice.1 growth
  intro p s m L hs hm hr
  filter_upwards [docket.purse s p m hs hm hr, R.alloy.B.a.fits.deep.eventually_ge_atTop (max L (max s m))]
    with k uses ready N n start
  obtain ⟨someScene,allScenes⟩:=uses N n start
  refine ⟨someScene,?_⟩
  intro S scene j kj jN
  have prices:=allScenes S scene
  have cofinal:=ready.trans (R.alloy.B.a.fits.mono (show k ≤ j+1 by omega))
  have jobs:max s m ≤ R.alloy.B.a.clock.J (j+1):=(le_max_right ..).trans cofinal
  have collar:L ≤ R.alloy.B.a.clock.J (j+1):=(le_max_left ..).trans cofinal
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG estate.sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have touched:=(MSbar.Ballet.validP R.family.path R.T.choice merit.towns N n _ jN).1
  exact physical_field_step R.alloy.B u V N k j n p m s S scene _ _ season
    (floorsP R.T N n _ jN) (floorsP R.T N n _ jN.le)
    (prices.2.2 _ (by omega) jN) hs jobs touched kj jN J L hG
    (fields.pay j n s p m L collar hs ((le_max_left ..).trans jobs) hm ((le_max_right ..).trans jobs) hr)
    estate.levy merit (prices.1 _ (by omega) jN)


/-- The forest and bits used in the existential form are the witnesses of the same realized
scene's step. In particular their selection is independent of the lamps and their marker subset. -/
theorem actual_field_ports_on (J:κ→Lamp G) (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (fields:fieldInvoice u V J R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    RealizedPorts J R u V := by
  have pinned:=actual_field_ports_pinned_on J hG R u V fields invoice
  intro p s m L hs hm hr
  filter_upwards [pinned p s m L hs hm hr] with k receipt N n kn
  obtain ⟨scene,prices⟩:=receipt N n kn
  refine ⟨scene,?_⟩
  intro S realized j kj jN
  exact ⟨(realized.step j jN kj).choose,(realized.step j jN kj).choose_spec.choose,prices S realized j kj jN⟩

/-- Pay the regular conditional comparison together with any other obtainable
objective using the same physical family and the given coordinate voice. -/
theorem actual_field_ports (J:κ→Lamp G) {goal:Goal G} (extra:Obtainable goal)
    (hG:G.Simple) (u:G.ColorIndex) (V:Voice G) (clear:Clear G V) (penalty:ℝ) (pos:0 < penalty) :
    ∃ R:PhysicalNext.Repeat.Legato.Run G,
      R.family.path.levels.clock.kernel.penalty=penalty ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels ∧ RealizedPorts J R u V := by
  let offer:=((extra.also Qlocal.Schedule.fixedWilsonChart_obtainable).also
    (fieldInvoice_obtainable hG u V clear J)).also (Qlocal.Schedule.vacuumInvoice_obtainable hG u V clear)
  obtain ⟨R,pen,⟨⟨grant,frame⟩,fields⟩,invoice⟩:=PhysicalNext.Repeat.Legato.Run.rampK hG offer penalty pos
  obtain ⟨docket,poetry⟩:=Qlocal.Schedule.docket_of_invoice hG R u V invoice
  exact ⟨R,pen,grant,frame,docket,poetry,actual_field_ports_on J hG R u V fields invoice⟩

end YM.Integration.FVA1Physical.Round2.Curvature
