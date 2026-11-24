import YM.Integration.OriginalMarkedFiniteRegularMenu
import YM.Integration.OriginalMarkedBirthRows
import YM.Integration.RunPhysicalMarks

/-! The finite full regular Q source on the original physical carrier with a
single explicit stage fee selected before upper cutoffs, periods and tests. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedCooledBirth
open Function Finset Lattice Wilson RG RG.Shoot Marker FVA1 MergeProof Menu
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail
open scoped Classical BigOperators

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [Fintype V] [DecidableEq V]
  (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B) (J : Request V)
  (A : NumericSchedule R.family J)
local notation "S" => ActualOriginalQInitialInput.schedule R hG u J A

def fee (m : ℕ) : ℝ :=
  ∑k∈Finset.range (ActualOriginalQPointCover.bound R u+1),
    |OriginalMarkedFiniteRegularMenu.cost (V:=V) G (R.family.path.levels.budget (m+1))
      (ActualOriginalQLayout.rankCap R u) 0 k ((S).inputWidth m) 1|

variable (z : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
  (o : V→Site (R.family.side (z.level+1) z.period)) (μ : ℝ) (orders : V→ℕ)
local notation "Γ" => Stock.census V
local notation "D" => ActualOriginalQPointSetup.pointDatum R J z.period (z.level+1) o
local notation "roots" => ActualOriginalQPackets.positions (D) u
local notation "Y" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "M" => ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
local notation "E" => OriginalMarkedBirthRows.active R hG u J A z Q o μ orders
local notation "g" => regulatorRun R.family z.cutoff z.period (z.level+1)
local notation "offset" => ActualOriginalQPackets.packetCover Q (D) u (μ-R.family.S.scale z.cutoff) orders z.cutoff (Y).p
variable (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests)

theorem frozen (U : Config G (R.family.side (z.level+1) z.period)) :
    source (M) (Y).p (g) x 1 U=source (M) (Y).p 1 x 1 U := by
  rw [ManuscriptQLocalOriginalConditionalTail.physical (M) (Y).p (g) x U,
    ManuscriptQLocalOriginalConditionalTail.physical (M) (Y).p 1 x U]
  apply tsum_congr
  intro i
  have fields := funext fun T=>OriginalMarkedBirthRows.field R hG u J A z Q o μ orders
    (testInclusion _ x) (g) T i.val
  unfold ManuscriptQLocalOriginalConditionalTail.field
  rw [fields]

theorem enrolled :
    ∃ (slot : (E)→ℕ) (m : (E)×Bool→Menu.Hat Γ (Y)),
      (∀i s,(m (i,s)).s=(M).mode i ∧ Menu.WKey (m (i,s))=.logKey (slot i)) ∧
      Menu.Offer (roots).origin m (fun _=>1) (Y).p.B (Y).p.supportExponent (fee R hG u J A z.level) ∧
      (∀U,GapsLocal.Full.given m 0 U=((Y).eval U:ℂ) • Poly.pass (source (M) (Y).p (g) x 1 U)) := by
  let C := R.family.path.levels.budget (z.level+1)
  let base (k : ℕ) := OriginalMarkedFiniteRegularMenu.cost (V:=V) G C
    (ActualOriginalQLayout.rankCap R u) 0 k ((S).inputWidth z.level) 1
  have actual := R.makes.wilson.represents z.cutoff z.period (z.level+1) (Nat.succ_le_of_lt z.below)
  have current : (Y).p=C := actual.vac
  have reserve := RunPhysicalMarks.actual_hasSlots R z.cutoff z.period (z.level+1) (Nat.succ_le_of_lt z.below)
  have H := OriginalMarkedBirthStencil.paid R hG u J A z Q o μ orders (Y).p 1
  obtain ⟨slot,m,keys,offer,all⟩ := OriginalMarkedFiniteRegularMenu.full (M) (Y) H
    (roots).origin (roots).mem (E) (OriginalMarkedBirthRows.present R hG u J A z Q o μ orders)
    actual.good.labels reserve x
  have within := OriginalMarkedBirthStencil.covered R u J z Q o μ orders (Y).p
  have run : OriginalMarkedFiniteRegularMenu.cost (V:=V) G (Y).p (M).rankCap (M).powerCap
      (offset) ((S).inputWidth z.level) 1 ≤ fee R hG u J A z.level := by
    change _ ≤ ∑k∈Finset.range (ActualOriginalQPointCover.bound R u+1),|base k|
    have value : OriginalMarkedFiniteRegularMenu.cost (V:=V) G (Y).p (M).rankCap (M).powerCap
        (offset) ((S).inputWidth z.level) 1 = base (offset) := by
      change OriginalMarkedFiniteRegularMenu.cost (V:=V) G (Y).p _ 0 _ _ _ = _
      unfold base
      rw [current]
      rfl
    rw [value]
    exact (le_abs_self _).trans (Finset.single_le_sum (fun k _=>abs_nonneg (base k))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le within)))
  refine ⟨slot,m,keys,Menu.Offer.fatten offer run,?_⟩
  intro U
  rw [frozen R hG u J A z Q o μ orders x U]
  exact all U

end YM.Integration.OriginalMarkedCooledBirth
end
