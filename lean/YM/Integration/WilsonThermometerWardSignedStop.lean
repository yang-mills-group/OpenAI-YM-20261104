import YM.Integration.WilsonThermometerReflectedTwoBills
import YM.Integration.WilsonThermometerWardPaidFaces
/-! Price both actual signed stores against the earlier filing of the Ward-restored field on its original Wilson history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardSignedStop
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
variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k u j:ℕ}
local notation "C" => R.family
local notation "z" => ((N,per):UVIndex)
local notation "X" => Config G ((C).side i per)
local notation "Z" => Cut (C) N per
local notation "H" => R.family.path
open private scaled from YM.Integration.WilsonThermometerReflectedWithdrawal
open private smooth_sum from YM.Integration.WilsonThermometerUnitFilingCylinder
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (bank:D.Tab R.rolls) (ticket:TicketP R.alloy R.kit D bank)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ a,RG.Rep G (R.family.side a per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (live:i≤N) (floor:m≤u) (age:u ≤ i)
  (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)

local notation "V" => Ψ i
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "κ" => LocalComparison.forcedDivisor R.family i

include way D bank ticket π Γ course floor gate in
theorem original {ι:Type} [Fintype ι] [Nonempty ι] (c:ι→ℂ) (physical corrected:ι→Z)
    (contF:∀s,Continuous (physical s)) (contH:∀s,Continuous (corrected s)) (price:ι→ℝ)
    (ju:j≤u) (door:Opened R.family 0 u per)
    (booked:∀s,Booked R.family N per 0 (corrected s) u (age.trans live))
    (tickets:∀s,PaidAt R.family.S N per j (R.family.beta N per) (price s)
      (physical s-report R (corrected s) u • (1:Z)))
    (y:Site ((C).side i per)) (model:X→ℂ) (a d:ℂ) (b h:Coefficient (F) ((C).side i per))
    {L M:ℝ} (lp:0≤L) (mp:0≤M) (fb:b.Format y (Y) (V)) (fh:h.Format y (Y) (V))
    (pb:b.remBound y (V) κ L) (ph:h.remBound y (V) κ M)
    (actual:∀U,(∑s,c s*credit R.family N per 0 (corrected s) i live U)-model U=
      a*h.density y (S) (V) U+d*b.density y (S) (V) U) :
    ‖(∑s,c s*R.family.omega N per (physical s))-WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u age‖≤
      (∑s,‖c s‖*price s)+(‖a‖*(‖h.x 0‖+5*M)+‖d‖*(‖b.x 0‖+5*L)):=by
  obtain ⟨book,reflect⟩:=WilsonThermometerWardPaidFaces.original R simple c corrected physical contH contF ju
    (age.trans live) door price booked tickets
  let Y₀:=∑s,c s • corrected s
  let f:=h.density y (S) (V)
  let g:=b.density y (S) (V)
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
    have creditSum:=IntrinsicProductLinearity.credit_sum R.family N per 0 i live c corrected contH
    simp only [Pi.sub_apply,Y₀,creditSum,Finset.sum_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,f,g]
    exact actual U
  have paid:‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (credit R.family N per 0 Y₀ i live-model) u age‖≤
      ‖a‖*(‖h.x 0‖+5*M)+‖d‖*(‖b.x 0‖+5*L):=by
    rw [eq,WilsonThermometerUnitFilingRaw.add R (N:=N) (a • f) (d • g) (eh.smul a) (eb.smul d) age,
      scaled R a f eh age,scaled R d g eb age]
    refine (norm_add_le ..).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left rh (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left rb (norm_nonneg _)
  have older:=WilsonThermometerUnitFilingRelativeStop.original R simple live age Y₀
    (smooth_sum R (N,per) c corrected contH) model (eq ▸ (eh.smul a).add (eb.smul d))
    paid door book
  exact (norm_sub_le_norm_sub_add_norm_sub _ (report R Y₀ u) _).trans (add_le_add reflect older)


end YM.Integration.WilsonThermometerWardSignedStop
