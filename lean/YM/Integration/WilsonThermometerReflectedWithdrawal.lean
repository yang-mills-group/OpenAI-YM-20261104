import YM.Integration.WilsonThermometerNominatedFaceCylinder
import YM.Integration.WilsonThermometerUnitFilingRelativeStop

/-! A whole compensated proper source on the older physical filing, with both of its actual hard stores. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerReflectedWithdrawal
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
private theorem scaled (a:ℂ) (f:X→ℂ) (integrable:Integrable f (prior G _)) (age:u ≤ i) :
    WilsonThermometerUnitFilingCoarse.reading R (N:=N) (a • f) u age=a*WilsonThermometerUnitFilingCoarse.reading R (N:=N) f u age := by
  have eq:gust H N per i (a • f) u age = a • gust H N per i f u age:=by
    induction age using Nat.decreasingInduction with
    | self => rw [gust_base,gust_base]
    | of_succ b sb ih =>
      rw [gust_step H N per i _ sb,ih,gust_step H N per i f sb]
      exact ((H).levels.clock.op b per).push_smul _ _ _ (gust_live H N per i f integrable sb)
  unfold WilsonThermometerUnitFilingCoarse.reading;rw [eq];simp only [Pi.smul_apply,smul_eq_mul];ring

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

include way D bank ticket π Γ course floor gate in
theorem original (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z)
    (ju:j≤u) (door:Opened R.family 0 u per) (c:(J₃).Mode→ℂ) (price:(J₃).Mode→ℝ)
    (arms:∀s,c s≠0→Booked R.family N per 0 (arm s) u (age.trans live) ∧
      PaidAt R.family.S N per j (R.family.beta N per) (price s)
        ((arm s)-report R (arm s) u • (1:Z)))
    (y:Site ((C).side i per)) (model:X→ℂ) (a:ℂ) (b h:Coefficient (F) ((C).side i per))
    {L M:ℝ} (lp:0≤L) (mp:0≤M) (fb:b.Format y (Y) (V)) (fh:h.Format y (Y) (V))
    (pb:b.remBound y (V) κ L) (ph:h.remBound y (V) κ M)
    (actual:∀U,take c (incoming R A simple live o U) - model U=
      a*(h.density y (S) (V) U-b.density y (S) (V) U)) :
    ‖take c (measured R A z o.origin)-WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u age‖ ≤
      (∑s,‖c s‖*price s)+‖a‖*((‖h.x 0‖+5*M)+(‖b.x 0‖+5*L)):=by
  obtain ⟨book,reflect⟩:=WilsonThermometerNominatedFaceCylinder.heard R A simple o c ju age live door price arms
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
  have eq:credit R.family N per 0 Y₀ i live-model=a • (f-g):=by
    funext U
    simp only [Pi.sub_apply,Y₀,WilsonThermometerNominatedFaceCylinder.condition R A simple o qual live,
      Pi.smul_apply,smul_eq_mul,f,g]
    exact actual U
  have minus:WilsonThermometerUnitFilingCoarse.reading R (N:=N) (f-g) u age=WilsonThermometerUnitFilingCoarse.reading R (N:=N) f u age-WilsonThermometerUnitFilingCoarse.reading R (N:=N) g u age:=by
    have add:=WilsonThermometerUnitFilingRaw.add R (N:=N) (f-g) g (eh.sub eb) eb age
    rw [sub_add_cancel] at add
    exact eq_sub_of_add_eq add.symm
  have paid:‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit R.family N per 0 Y₀ i live-model) u age‖≤
      ‖a‖*((‖h.x 0‖+5*M)+(‖b.x 0‖+5*L)):=by
    rw [eq,scaled R a (f-g) (eh.sub eb) age,minus,norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add rh rb)) (norm_nonneg _)
  have older:=WilsonThermometerUnitFilingRelativeStop.original R simple live age Y₀
    (WilsonThermometerNominatedFaceCylinder.smooth R A o c) model (eq ▸ (eh.sub eb).smul a)
    paid door book
  exact (norm_sub_le_norm_sub_add_norm_sub _ (report R Y₀ u) _).trans (add_le_add reflect older)

end YM.Integration.WilsonThermometerReflectedWithdrawal
