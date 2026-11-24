import YM.Integration.WilsonCenteredCloseOccupiedSale
import YM.Integration.WilsonThermometerReceivedScalar

/-! At geometric capture the entire paid thermometer on the true marked
post has one polynomially bounded residual, at the reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerHaloScalar
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
open RG16 RG16.Literal

open FVA1 OriginalForcedAddresses WilsonThermometerCourseHearing WilsonThermometerCourseIntake
open WilsonPositionThermometerCapStation WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open WilsonCenteredCloseOccupiedSale WilsonCenteredCloseCaptureWallet
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ)
  (ahead : Mentor.Forecast D R.rolls bank φ books)
  (order shelf seats : ℕ) (mb : m ≤ b) (cutoff : b<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "C" => R.family
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "source" => offered R A simple cutoff o
local notation "history" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R disks source i ib
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params

private theorem genuine {i : ℕ} (ib : i ≤ b) : (history i ib) fired = incoming R A simple (ib.trans_lt cutoff) o := by
  induction ib using Nat.decreasingInduction with
  | self => rw [WilsonReceivedCloseHistory.head];exact fired_input R A simple cutoff o
  | of_succ j jb ih =>
    rw [←congrFun (WilsonReceivedCloseHistory.adjacent (N:=N) R disks source jb) fired,ih,
      WilsonThermometerCourseIntake.step]

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (initial : post b mb source) (h : ℕ) (U α : ℝ) (income : 0 ≤ U)
    (paid : WilsonReceivedCloseNamedWallet.Sold R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats
      mb source initial univ (U*((g b)⁻¹)^h))
    (degree : ℕ) (cap : ℝ) (close : PaceR.Close R degree cap m b)
    (travel : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (gallery : (eventually_atTop.mp (WilsonReceivedCloseGalleryWallet.reserve R simple (max 1 3)
      (show (0:ℝ) < 1 by norm_num))).choose ≤ m)
    (slow : ∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (rays : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ m)
    (before : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ m)
    (eligible : WilsonCenteredCaptureClock.first R simple ≤ m)
    (way : WayStation R.kit) (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    {i : ℕ} (ib : i ≤ b) (mi : m ≤ i) (L : post i mi (history i ib))
    (trail : WilsonReceivedCloseHistory.Trail R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats
      mb source initial i mi (history i ib) L)
    (stages : shelf ≤ R.alloy.B.a.clock.J i) (size : L.op.count ≤ Burn.horizon k+2)
    (support : (R.family.path.levels.budget i).supportExponent ≤ α)
    (sec : R.t 0 ≤ i) (refs : ∀ j:Fin 3,(C).ref (WilsonPositionThermometerGradedSource.grade j) ≤ N)
    (Z : Support ((C).side i per)) (y: Site ((C).side i per)) (rad : ℕ) (center : y∈Z)
    (home : ∀ j:Fin 3,(L.passport.coarser (move i).ratio).origin j∈Z)
    (near : ∀ j:Fin 3,separation ((L.passport.coarser (move i).ratio).origin j) y ≤ rad)
    (short : rad ≤ ((C).path.levels.budget i).B) (inside : Z⊆halo ((C).path.levels.budget i).B {y})
    (Q : Poly J) (t : ℝ) (invoice : ℕ) (banked : (g (i+1))^invoice*(∑ s:(J).Mode,‖weight Q s‖) ≤ t) :
    let price:=WilsonCenteredCloseOccupiedSale.amount G 0 seats h 3 α U
    let e:=exponent seats h 3
    let κ:=LocalComparison.forcedDivisor (C) i
    ∃ q:Coefficient (F) ((C).side i per), q.Format y (Y) (Ψ i) ∧
      q.remBound y (Ψ i) κ (t*price/(g (i+1))^(invoice+e)) ∧
      credit (C) N per 0 (WilsonThermometerLiteralCredit.cut R A o Q) i (ib.trans_lt cutoff).le=q.density y (S) (Ψ i) ∧
      ∀ B, q.density y (S) (Ψ i) B=(total (incoming R A simple (ib.trans_lt cutoff).le o B) Q).part full := by
  intro price e κ
  let gs:=g (i+1)
  let fees (_:(J).Mode):= price/gs^e
  have gpos : 0<gs:=ActualRunKernelPackets.regulator_pos R N per (i+1) (ib.trans_lt cutoff)
  have price0 : 0 ≤ price:=by
    dsimp only [price,WilsonCenteredCloseOccupiedSale.amount,WilsonCenteredPhysicalFare.base,WilsonCenteredAllMaskCeiling.scale,
      WilsonCenteredCloseCaptureWallet.price]
    positivity
  have push : LocalComparison.actualPush (C) N per i ((history i ib) fired) = incoming R A simple (ib.trans_lt cutoff).le o := by
    rw [genuine,WilsonThermometerCourseIntake.step]
  have stocked (s:(J).Mode) : ∃ a:Coefficient (F) ((C).side i per), a.Format y (Y) (Ψ i) ∧
      a.remBound y (Ψ i) κ (fees s) ∧
      ∀ B, a.density y (S) (Ψ i) B=(incoming R A simple (ib.trans_lt cutoff).le o B).part s := by
    obtain ⟨a,form,rem,field,-⟩:=WilsonCenteredCloseOccupiedSale.original R simple hk D bank π Γ Ψ books ahead
      disks sectors ages order shelf seats mb source course initial cutoff univ h 3 (by decide) U α income paid
      degree cap close travel gallery slow ready rays before eligible way pass hospital ib mi L trail stages size support 0 sec
      fired s (Finset.subset_univ _) ((Finset.card_le_card (Finset.subset_univ s.val)).trans (by decide)) ∅ (fun _=>0)
      (by simp) Z y rad center (fun j _=>home j) (by simp) (fun j _=>near j) (by simp) short inside
    simp only [sum_empty,add_zero,one_mul] at rem
    refine ⟨a,form,rem,fun z=>?_⟩
    have entry:=field z
    simp only [push,sum_empty,sub_zero] at entry
    exact entry
  choose a form rem density using stocked
  have walk:=course.1.walk i mi (ib.trans_lt cutoff).le
  obtain ⟨fmt,bill,-,-,heard⟩:=deposited R A simple (ib.trans_lt cutoff).le o (Ψ i) y a Q
    (Real.sqrt_pos.mpr (Real.exp_pos _)) walk.truep.valid fees form rem density
  have paid' : (∑ s:(J).Mode, ‖weight Q s‖) ≤ t/gs^invoice :=
    (le_div_iff₀ (pow_pos gpos _)).mpr (by simpa [mul_comm] using banked)
  have cost : (∑ s,‖weight Q s‖*fees s) ≤ t*price/gs^(invoice+e) := calc
    _ = (∑s:(J).Mode, ‖weight Q s‖)*(price/gs^e) := (sum_mul ..).symm
    _ ≤ (t/gs^invoice)*(price/gs^e):=mul_le_mul_of_nonneg_right paid' (div_nonneg price0 (pow_nonneg gpos.le _))
    _ = _ :=by rw [pow_add];ring
  obtain ⟨a₀,a₁,n₀,n₁,sum,rest⟩:=bill
  exact ⟨_,fmt,⟨a₀,a₁,n₀,n₁,sum.trans cost,rest⟩,(WilsonThermometerLiteralCredit.returned R A simple o Q refs _).trans
    (funext heard).symm,heard⟩
end YM.Integration.WilsonThermometerHaloScalar
