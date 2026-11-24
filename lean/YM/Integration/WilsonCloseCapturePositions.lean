import YM.Integration.WilsonCloseCaptureFinances
import YM.RG05Readout.UV.Positions

/-! The signed off-center price for every original ultraviolet gauge door of the already chosen Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCapturePositions
open Filter Set Lattice RG Wilson Source Labels PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open YM.UVExtension UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Bid Planned.GuardedAtom Guard Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bandage
open WilsonLimitConstruction RG05Readout RG05Readout.Address
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple)

/-- The historical port uses the original physical history recorded before the slot-field extension. -/
def port (R : Run G) : Vintage.YM.Org.Bolt R.alloy := by
  let A := R.alloy
  let V := R.T.history
  let X := A.B.bake.make V
  have h := R.T.sticks
  have live (N p i : ℕ) (hi : i≤N) : Lives A.B.bake N i p (V N p i) := ((h N p).prices i (Nat.zero_le _) hi).1
  have supplied (N p i : ℕ) (hi : i≤N) : X.Conv N p i :=
    ⟨(live N p i hi).point,(live N p i hi).clip,(live N p i hi).valid,((h N p).prices i (Nat.zero_le _) hi).2⟩
  have transfer (N p i : ℕ) (hi : i<N) : X.Transfer N p i :=
    ⟨((h N p).persists i (Nat.zero_le _) hi).link,((h N p).persists i (Nat.zero_le _) hi).drift⟩
  exact ⟨R.T.program,V,h,⟨fun N p q m hm => (live N p m hm).path.trans (live N q m hm).path.symm,
    supplied,fun N p => ⟨(h N p).fromTop.scalars,(h N p).fromTop.raw⟩,
    transfer,fun _ _ => trivial,traject X supplied transfer⟩,R.T.moves⟩

theorem nested : Vintage.YM.PhysicalNext.Repeat.Graces.Nest R.kit (port R) :=
  ⟨R.tuning.receipts.born,R.tuning.receipts.held⟩

include hG
theorem positions (purchase : RG05Preconstruction.ReadoutPurchase R.b) (d N m p : ℕ)
    (hm : m<N) (hd : d+3≤R.alloy.B.a.clock.J m) :
    ∃ (T : Heading (R.family.labels.level d)) (a : ℝ),
      Pricing (R.family.localSection d) R.family.path N p m R.family.params (R.doors N p m hm) T a
        (R.y (R.alloy.B.a.clock.J (m+1))) (Doors.rate (R.alloy.B.a.S.block m))
        (2*(Real.exp (R.family.path.rep N p (m+1)).p.supportExponent*Cub.title G (R.alloy.B.a.params (m+1)))) ∧
      Push.Local.triangularPrice (R.family.labels.level d) a ≤ R.y (R.alloy.B.a.clock.J (m+1)) := by
  obtain ⟨a⟩ := purchase.moved _ _ (R.alloy.B.valid.pays m) _ d (first_le R.alloy.B.valid m)
    (step_paid R.alloy.B.a m) hd
  obtain ⟨l,v,K,spring,x,base,fine,door⟩ := R.carries N m p hm
  have slots := R.tuning.receipts.samples hG N (m+1) p hm
  have old := R.tuning.receipts.samples hG N m p hm.le
  have fine_budget := (R.makes.wilson.represents N p (m+1) hm).vac
  have use_fine : (K x.val).p = R.alloy.B.a.budget (m+1) :=
    (congrArg Rep.p fine).symm.trans fine_budget
  have read : Push.Local.Readable (hol G) (localSection G d) (K x.val).p
      (R.alloy.B.a.S.side (m+1) p) (Cub.title G (R.metals.p.profile (R.alloy.B.a.clock.J (m+1)))) := by
    rw [use_fine]
    rw [show Cub.title G (R.metals.p.profile (R.alloy.B.a.clock.J (m+1))) =
      authors R.alloy.B.a (m+1) by unfold Cub.title authors;rw [params_eq R.alloy.B.valid] ]
    exact Graces.lively R.b.clock ((Nat.le_add_right d 3).trans (hd.trans (step_paid R.alloy.B.a m).1))
  rw [door]
  have fine_slots : HasSlots (K x.val).p (K x.val).activities := fine ▸ slots
  have base_slots : HasSlots (spring.result x.val).p (spring.result x.val).activities := base ▸ old
  have ticket := Cub.RG05_price (jV:=R.family.path.rep) hm R.b.songs R.b.PStage R.b.wait
    (Graces.feet hd R.b.clock) (nested R) R.b.r spring x base fine
    (R.makes.wilson.represents N p m hm.le) hG R.b.tunes R.b.furthering R.b.corners R.b.shape R.b.clock R.b.stamp
    read fine_slots (Keeper.sufficient base_slots) a hd
  have exponent : (R.family.path.rep N p (m+1)).p.supportExponent = (K x.val).p.supportExponent :=
    congrArg (fun z => z.p.supportExponent) fine
  rw [Push.PriceCompiler.block_eq R.alloy.B.valid m,Push.PriceCompiler.params_eq R.alloy.B.valid (m+1),exponent]
  exact ticket

end YM.Integration.WilsonCloseCapturePositions
