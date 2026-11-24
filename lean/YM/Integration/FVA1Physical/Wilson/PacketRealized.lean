import YM.Integration.FVA1Physical.Wilson.PacketInvoice
import YM.Integration.FVA1Physical.Wilson.SceneReceipt
import YM.Integration.FVA1Physical.Sources.Round2.FieldRealized

/-! Every realized Wilson scene on a single chosen construction shares its
prepaid action, covariance and physical clock with all rendered incoming packets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
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



open YM.Integration.FVA1Physical.Wilson YM.Integration YM.MSbar.Heath
open Exterior Tree MSbar.Rolling MSbar.Midpoint MSbar.Whisk Pressure

/-- The same realized forest that emits the vacuum acts on every
anchored incoming packet through the profile's full allowed degree. -/
def PinnedPacketPorts (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G) : Prop :=
      ∀ p s m:ℕ, 6 ≤ s → 4 ≤ m → p+2 ≤ m →
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
          ∀ (z:Site A.f) (Z:Positions (Primary A.c G)), ‖Z‖ ≤ Mosaic.hull x →
            InheritedPort A R.metals.O V p ((m+1)*(p+2)) y (y^Mosaic.pawn p) z Z

/-- Consume the prices on an already-selected construction and fixed chart voice.
Additional invoices may have been purchased before choosing this Run. -/
theorem packet_ports_pinned_on (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (fields:packetInvoice u V R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedPacketPorts R u V := by
  have docket:=(Qlocal.Schedule.docket_of_invoice hG R u V invoice).1
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  have estate:=invoice.1 growth
  intro p s m hs hm hr
  filter_upwards [docket.purse s p m hs hm hr, R.alloy.B.a.fits.deep.eventually_ge_atTop (max s m)]
    with k uses ready N n start
  obtain ⟨someScene,allScenes⟩:=uses N n start
  refine ⟨someScene,?_⟩
  intro S scene j kj jN
  have prices:=allScenes S scene
  have cofinal:=ready.trans (R.alloy.B.a.fits.mono (show k ≤ j+1 by omega))
  have jobs:max s m ≤ R.alloy.B.a.clock.J (j+1):=cofinal
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG estate.sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have touched:=(MSbar.Ballet.validP R.family.path R.T.choice merit.towns N n _ jN).1
  let goal:=fun A : MSbar.Mosaic.Issue G=> ∀ (z:Site A.f) (Z:Positions (Primary A.c G)),
    ‖Z‖ ≤ MSbar.Mosaic.hull (R.alloy.B.a.clock.hatBeta j) →
    InheritedPort A R.metals.O V p ((m+1)*(p+2)) (R.alloy.B.a.clock.hatBeta (j+1))
       ((R.alloy.B.a.clock.hatBeta (j+1))^MSbar.Mosaic.pawn p) z Z
  apply apply_scene_receipt R.alloy.B u V N k j n p m s S scene _ _ season
    (floorsP R.T N n _ jN) (floorsP R.T N n _ jN.le)
    (prices.2.2 _ (by omega) jN) hs jobs touched kj jN goal hG _ estate.levy merit (prices.1 _ (by omega) jN)
  intro branch
  obtain ⟨Z,card⟩:=fields.pay j n s p m hs ((le_max_left ..).trans jobs) hm ((le_max_right ..).trans jobs) hr branch
  refine ⟨Z,card.ordinary,?_⟩
  intro A paid kernel fest clk cs cost
  have q:=card.fields A paid kernel fest clk cs cost
  have y : R.alloy.B.a.clock.hatBeta (j+1)=MSbar.Heath.Stock.tip G (R.alloy.B.a.clock.op j n).patch.L
      (R.alloy.B.a.clock.hatBeta j) := Extra.Iteration.block_beta (a:=R.family.path.levels) j
  dsimp only [goal];rw [y];exact q

end YM.Integration.FVA1Physical.Wilson
