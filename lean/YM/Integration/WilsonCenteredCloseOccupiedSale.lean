import YM.Integration.WilsonCenteredReceivedAggregate
import YM.Integration.WilsonCenteredMeasuredOccupiedSale
import YM.Integration.WilsonCenteredCloseCaptureWallet
import YM.Integration.WilsonCapturedPrimarySection

/-! The genuine measured source at every date of the original close course. The
one coordinate contains all properly deposited and disconnected subwords, and
the chosen paid radius bounds its regular and full compulsory income together. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCloseOccupiedSale
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
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
local notation "history" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


def exponent (seats sourcePower load : ℕ) :=
  WilsonCenteredPhysicalFare.degree seats (WilsonCenteredCloseCaptureWallet.width sourcePower load)*(3*load+9)

def amount (G : Gauge) (d seats sourcePower load : ℕ) (α U : ℝ) :=
  WilsonCenteredAllMaskCeiling.scale load*
    (WilsonCenteredPhysicalFare.base (localSection G d) (hol G) α
      (WilsonCenteredCloseCaptureWallet.price U sourcePower load) seats)^(3*load+9)

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (initial : post b mb source) (cutoff : b < N) (active : Finset V) (h load : ℕ) (occupied : 1 ≤ load)
    (U α : ℝ) (income : 0 ≤ U)
    (paid : WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial active (U*((g b)⁻¹)^h))
    (degree : ℕ) (cap : ℝ) (close : PaceR.Close R degree cap m b)
    (travel : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (gallery : (eventually_atTop.mp (WilsonReceivedCloseGalleryWallet.reserve R simple (max 1 load)
      (show (0:ℝ) < 1 by norm_num))).choose ≤ m)
    (slow : ∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (rays : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ m)
    (before : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ m)
    (eligible : WilsonCenteredCaptureClock.first R simple ≤ m)
    (way : WayStation R.kit) (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    {i : ℕ} (ib : i ≤ b) (mi : m ≤ i) (L : post i mi (history i ib))
    (trail : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial i mi (history i ib) L)
    (stages : shelf ≤ R.alloy.B.a.clock.J i) (size : L.op.count ≤ Burn.horizon k+2)
    (support : (R.family.path.levels.budget i).supportExponent ≤ α)
    (d : ℕ) (sectionReady : R.t d ≤ i)
    (x : Wallet actors) (s : (Stock.census V).Mode) (selected : s.val ⊆ active) (fixed : s.val.card ≤ load)
    (names : Finset V) (c : V → ℂ) (stored : names ⊆ active)
    (Z : Support (R.family.side i per)) (y : Site (R.family.side i per)) (rad : ℕ) (center : y ∈ Z)
    (home : ∀j ∈ s.val,(L.passport.coarser (move i).ratio).origin j ∈ Z)
    (zc : ∀j ∈ names,(L.passport.coarser (move i).ratio).origin j ∈ Z)
    (near : ∀j ∈ s.val,separation ((L.passport.coarser (move i).ratio).origin j) y ≤ rad)
    (nc : ∀j ∈ names,separation ((L.passport.coarser (move i).ratio).origin j) y ≤ rad)
    (short : rad ≤ (R.family.path.levels.budget i).B) (halo : Z ⊆ Lattice.halo (R.family.path.levels.budget i).B {y}) :
    let frame := (Labels.frames G).level d
    let push := LocalComparison.actualPush R.family N per i ((history i ib) x)
    let reading := fun U => (push U).part s-∑j ∈ names,c j*(push U).part ((Stock.census V).fire j)
    ∃ q : Coefficient frame (R.family.side i per), q.Format y (hol G) (Ψ i) ∧
      q.remBound y (Ψ i) (LocalComparison.forcedDivisor R.family i)
        ((1+∑j ∈ names,‖c j‖)*amount G d seats h load α U/(g (i+1))^(exponent seats h load)) ∧
      (∀U,q.density y (localSection G d) (Ψ i) U=reading U) ∧
      ∀probe:Probe G d,probe.2.val=0 → runProbe frame probe q.x=((Ψ i).eval 1:ℂ)⁻¹*reading 1 :=by
  dsimp only
  have point := (course.1.walk i mi (ib.trans cutoff.le)).truep.point
  have reader := (WilsonCapturedPrimarySection.original R sectionReady (Ψ i) point).1
  obtain ⟨q,form,rem,eq,scalar⟩ := WilsonCenteredReceivedAggregate.original R hk D Q π Γ Ψ course books mi
    (ib.trans_lt cutoff) ahead actors pieces grades order shelf seats (history i ib) L way simple (eligible.trans mi)
    x s names c Z y center home zc rad near nc (localSection G d) (hol G) reader
  have clock := (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i
    (rays.trans mi) N per (ib.trans_lt cutoff)
  have W := WilsonCenteredCloseCaptureWallet.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source initial cutoff.le simple degree h load occupied cap U income close travel gallery paid ib mi
    (ib.trans_lt cutoff) L trail clock.1
  have Wpos : 0 ≤ WilsonCenteredCloseCaptureWallet.price U h load :=by
    unfold WilsonCenteredCloseCaptureWallet.price
    positivity
  have fare := WilsonCenteredMeasuredOccupiedSale.original R hk D Q π Γ Ψ course books mi (ib.trans_lt cutoff)
    ahead actors pieces grades order shelf seats (history i ib) L way simple slow ready (rays.trans mi) (before.trans mi)
    pass hospital stages size s names c Z y rad (WilsonCenteredCloseCaptureWallet.width h load) d load Wpos
    (point ▸ support) (point ▸ short) (point ▸ halo) fixed
    (fun t ht=>W.2 t (ht.trans selected) ((card_le_card ht).trans fixed))
    (fun j hj=>W.2 _ (singleton_subset_iff.mpr (stored hj)) (by simpa [Census.fire] using occupied))
  obtain ⟨a,b,ha,hb,total,rest⟩:=rem
  exact ⟨q,form,⟨a,b,ha,hb,total.trans fare,rest⟩,eq,scalar⟩

end YM.Integration.WilsonCenteredCloseOccupiedSale
