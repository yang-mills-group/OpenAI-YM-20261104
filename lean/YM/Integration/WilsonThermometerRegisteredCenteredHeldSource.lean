import YM.Integration.WilsonThermometerReflectedTwoBills

/-! Signed linear weights on two complete original withdrawals at a reflected older filing. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredHeldSource
open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Marker QuadraticLocal
open Extra.Histories Extra.Histories.Relay Extra.Trajectories Extra.Multi MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit
open WheelP QuadraticLocal.Advent FVA1 RG12 RG16 RG16.Literal
open Table Spec Trace Trace.Pilot Extraction Climb Next.UVStress Trace.Physical.GermGraph Cells
open WilsonThermometerCourseIntake WilsonGeometricSignedCapture WilsonThermometerFiniteConnectedCells
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFeed
open WilsonPositionThermometerCapStation PhysMS RG17 OPE.Cards
open PhysicalNext PhysicalNext.Repeat Legato Org AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler
open RemainderComparison Tree
open scoped BigOperators Topology Classical
local notation "J₃" => Stock.census (Fin 3)
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple) {m i N per k u j:ℕ}
local notation "C" => R.family
local notation "z" => ((N,per):UVIndex)
local notation "X" => Config G ((C).side i per)
local notation "Z" => Cut (C) N per
local notation "H" => R.family.path
open private scaled from YM.Integration.WilsonThermometerReflectedWithdrawal
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (bank:D.Tab R.rolls) (ticket:TicketP R.alloy R.kit D bank)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ a,RG.Rep G (R.family.side a per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (live:i≤N) (floor:m≤u) (age:u ≤ i)
  (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)
  (o:FVA1.Positions (Fin 3) (R.family.side N per))
local notation "V" => Ψ i
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "arm" s:max => placed R A z (s).val o.origin
local notation "cut" c:max => WilsonThermometerNominatedFaceCylinder.source R A o c

def originalCredit (c:(J₃).Mode→ℂ) (un:u≤N):ℂ:=
  (((C).path.rep N per u).eval (1:Config G ((C).side u per)):ℂ)⁻¹*credit (C) N per 0 (cut c) u un 1

include way D bank ticket π Γ course floor gate in
theorem original (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z)
    (c:(J₃).Mode→ℂ)
    (y:Site ((C).side i per)) (model:X→ℂ) (a d:ℂ) (b h:Coefficient (F) ((C).side i per))
    {L M:ℝ} (lp:0≤L) (mp:0≤M) (fb:b.Format y (Y) (V)) (fh:h.Format y (Y) (V))
    (pb:b.remBound y (V) κ L) (ph:h.remBound y (V) κ M)
    (actual:∀U,take c (incoming R A simple live o U) - model U=
      a*h.density y (S) (V) U+d*b.density y (S) (V) U) :
    ‖originalCredit R A o c (age.trans live)-WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u age‖≤
      ‖a‖*(‖h.x 0‖+5*M)+‖d‖*(‖b.x 0‖+5*L):=by
  let f:=h.density y (S) (V)
  let g:=b.density y (S) (V)
  let Y₀:=cut c
  have eh:Integrable f (prior G _):=(WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course
    (floor.trans age) live (S) (Y) y h fh ph).2
  have eb:Integrable g (prior G _):=(WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course
    (floor.trans age) live (S) (Y) y b fb pb).2
  have rh:=(WilsonThermometerUnitFilingWhole.original R simple way D bank ticket π Γ Ψ course
    live floor age gate y h fh ph mp).1 u le_rfl age
  have rb:=(WilsonThermometerUnitFilingWhole.original R simple way D bank ticket π Γ Ψ course
    live floor age gate y b fb pb lp).1 u le_rfl age
  have eq:credit R.family N per 0 Y₀ i live-model=a • f+d • g:=by
    funext U
    simp only [Pi.sub_apply,Y₀,WilsonThermometerNominatedFaceCylinder.condition R A simple o qual live,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul,f,g]
    exact actual U
  have paid:‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (credit R.family N per 0 Y₀ i live-model) u age‖≤
      ‖a‖*(‖h.x 0‖+5*M)+‖d‖*(‖b.x 0‖+5*L):=by
    rw [eq,WilsonThermometerUnitFilingRaw.add R (N:=N) (a • f) (d • g) (eh.smul a) (eb.smul d) age,
      scaled R a f eh age,scaled R d g eb age]
    refine (norm_add_le ..).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left rh (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left rb (norm_nonneg _)
  let ear:=credit (C) N per 0 Y₀ i live
  have raw:Integrable (ear-model) (prior G _):=eq ▸ (eh.smul a).add (eb.smul d)
  have ht:=WilsonThermometerUnitFilingInvoice.credit_live R live Y₀
    (WilsonThermometerNominatedFaceCylinder.smooth R A o c)
  have hm:Integrable model (prior G _):=by
    have balance:ear-(ear-model)=model:=sub_sub_cancel _ _
    rw [←balance];exact ht.sub raw
  have split:=WilsonThermometerUnitFilingRaw.add R (N:=N) (ear-model) model raw hm age
  rw [sub_add_cancel] at split
  have whole:originalCredit R A o c (age.trans live)=WilsonThermometerUnitFilingCoarse.reading R (N:=N) ear u age:=by
    unfold WilsonThermometerUnitFilingCoarse.reading
    rw [WilsonThermometerUnitFilingCoarse.cutoff R live age Y₀ (WilsonThermometerNominatedFaceCylinder.smooth R A o c)]
    rfl
  rw [whole,split,add_sub_cancel_right];exact paid

end YM.Integration.WilsonThermometerRegisteredCenteredHeldSource
