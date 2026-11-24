import YM.Integration.WilsonReceivedCloseHistory
import YM.Next.RANK.Coordinates

/-! The dated passport at every genuine close post tracks the submitted
sites through the original physical schedule before its local halo is tested. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryTrailSites
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom
open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m  ≤  b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
local notation "history" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


theorem original (S : post b mb source) {i : ℕ} {mi : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : post i mi y} (traced : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source S i mi y L) : ∃ ib : i ≤ b, ∀v,
      L.passport.origin v=(R.family.S.toDepth (Nat.succ_le_succ ib) per).parent (S.passport.origin v) := by
  induction traced with
  | start =>
    refine ⟨le_rfl,fun v=>?_⟩
    let t := R.family.S.toDepth (le_refl (b+1)) per
    have unit:t.count.val=1:=Nat.eq_of_mul_eq_mul_left (R.family.S.side (b+1) per).property
      (t.exact_size.symm.trans (Nat.mul_one _).symm)
    have same:t.embed (S.passport.origin v)=S.passport.origin v := by
      rw [Ratio.embed,unit,one_smul,Lattice.wrap_lift]
    exact ((congrArg t.parent same).symm.trans (t.embed_parent _)).symm
  | step before loan factor one fee width ih =>
    obtain ⟨above,site⟩:=ih
    refine ⟨(Nat.le_succ _).trans above,fun v=>?_⟩
    rw [loan.passport]
    change (move _).ratio.parent _=_
    rw [site]
    exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.block_odd _)
      (R.family.S.toDepth_odd (Nat.succ_le_succ above) per) _).symm

theorem outgoing (S : post b mb source) {i : ℕ} (ib : i ≤ b) {mi : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : post i mi y} (traced : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source S i mi y L) (v : V) :
      (L.passport.coarser (move i).ratio).origin v =
        (R.family.S.toDepth (ib.trans (Nat.le_succ b)) per).parent (S.passport.origin v) := by
  obtain ⟨up,location⟩:=original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source S traced
  change (move i).ratio.parent _=_
  rw [location]
  exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.block_odd _)
      (R.family.S.toDepth_odd (Nat.succ_le_succ up) per) _).symm

end YM.Integration.WilsonCapturedPrimaryTrailSites
