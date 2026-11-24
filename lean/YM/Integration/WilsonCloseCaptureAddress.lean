import YM.Integration.WilsonCloseCapturePositions
import YM.RG05Readout.UV.Enamel

/-! The actual signed address of every emitted Wilson field on the original gauge door. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCaptureAddress
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

open RG05Readout.Copper RG05Readout.Native
variable {G : Gauge} (R : Run G) (hG : G.Simple)
local notation "C" => R.family
local notation "A" => R.alloy.B.a
include hG

theorem issued (purchase : RG05Preconstruction.ReadoutPurchase R.b)
    (d m N p : ℕ) (hm : m<N) (hd : d+3≤(A).clock.J m)
    (hit : Push.Local.hitWidth ((C).path.rep N p m).p*Push.Local.kappa (C).path m ≤ 1)
    (fine : Push.Local.kappa (C).path (m+1) ≤ 1) :
    ∃ T : ∀ i:Native.Letter d, Heading ((C).labels.level (kept i)),
      Address.Plot (R.doors N p m hm) (lumens G ((A).params m)) (optics G ((A).params m) d)
        (R.y ((A).clock.J (m+1))) (Doors.rate ((A).S.block m)) (swing G ((A).params (m+1))) T := by
  have budget (i : ℕ) (later : i≤N) : ((C).path.rep N p i).p = (A).budget i :=
    (R.makes.wilson.represents N p i later).vac
  have exponent (i : ℕ) (later : i≤N) :
      ((C).path.rep N p i).p.supportExponent = ((A).params i).supportExponent :=
    congrArg BudgetPoint.supportExponent (budget i later)
  have priced (z : ℕ) (zd : z≤d) : ∃ (T : Heading ((C).labels.level z)) (a : ℝ),
      Pricing ((C).localSection z) (C).path N p m (C).params (R.doors N p m hm) T a
        (R.y ((A).clock.J (m+1))) (Doors.rate ((A).S.block m)) (swing G ((A).params (m+1))) ∧
        Push.Local.triangularPrice ((C).labels.level z) a ≤ R.y ((A).clock.J (m+1)) := by
    obtain ⟨T,a,ticket,small⟩ := WilsonCloseCapturePositions.positions R hG purchase z N m p hm (by omega)
    rw [exponent (m+1) hm] at ticket
    exact ⟨T,a,ticket,small⟩
  choose T y hT using fun i:Native.Letter d => priced (kept i) (Nat.sub_le ..)
  obtain ⟨base,a,zero,za⟩ := priced 0 (Nat.zero_le _)
  obtain ⟨hk,ho,hp,hF,hS⟩ := (k_found G ((A).params m) d).choose_spec
  have tests (z : ℕ) (zd : z≤d) : Push.Local.Readable (C).params ((C).localSection z)
      ((C).path.rep N p m).p ((C).S.side m p) (lumens G ((A).params m)) := by
    have guard : z≤(A).clock.J m := by omega
    have size := Doors.Latch.lengths (R.b.clock.sequences m z guard) p
    have step := R.b.clock.stage m
    rw [budget m hm.le]
    exact Push.Local.foundation_readable G z (B:=(A).budget m) size (guard.trans step.1) (guard.trans step.2)
  have exp : ((C).path.rep N p m).p.supportExponent=((A).params m).supportExponent := exponent m hm.le
  refine ⟨T,⟨tests,?_,hp,hF,hk,hS,?_,hit⟩,
    zero.lower.price.trans ((triangle_cost1 _ zero.lower.price).trans za), (Doors.rate_pos _).le,
    ?_,fun i => ⟨y i,hT i⟩,⟨base,a,zero⟩,zero.soundD,fine⟩
  · rw [exp]; exact ho
  · exact ⟨Keeper.sufficient (R.tuning.receipts.samples hG N m p hm.le)⟩
  · unfold swing lumens
    exact mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Next.Foundations.price_one_le ..)))

end YM.Integration.WilsonCloseCaptureAddress
