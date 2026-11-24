import YM.Integration.WilsonReceivedDepositedVersePrinter
import YM.Integration.WilsonSeparatedOriginalThermometerCells

/-! An absolute microscopic cell selects one child at every occupied site.
The finite and folded angular fields are the two components of the same
fixed-position logO. Their signed winding bill uses the original joint
cell weights of the physical test. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicFixedCells
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket

open WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp Source Multi Table Cells MeasureTheory
open WilsonSeparatedOriginalThermometerCells (positions placed weight variation tested)
variable {G:Gauge}(R:Run G){j e N:ℕ}(per:ℕ){k D:Fin 3→ℕ}{S J:Finset (Fin 3)}{A:ℝ}
variable (Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor≤j)(older:j<N)(c:Fin 3)
local notation "fine" => R.family.side N per
local notation "coarse" => R.family.side j per
local notation "Cells₃" => (Fin 3 → Site (R.family.side N per))
def child (x:Cells₃):Fin 3 → Site (R.family.side (j+1) per):=
  (R.family.S.toDepth older per).parent ∘ x
def centers (x:Cells₃):Fin 3 → Site coarse:=
  (R.family.S.oneStep j per).parent ∘ child R per older x
def lifts (x:Cells₃):Fin 3 → Cover:=PeriodicMarkedWinding.roots coarse (centers R per older x) c

variable (X:(Fin 3 → Site (R.family.side N per)) → Input Y lo S k D A)(t:Case D)(a rank:ℕ)
variable (dirs:(Fin 3 → Site (R.family.side N per)) → Fin rank → Woods G (R.family.side j per))
local notation "row" x:max => FundedMarkedPathSelection.output (X x) J N (lifts R per older c x)

def left (x:Cells₃):ℂ:=by
  let y:Fin 3→ Cover:=lifts R per older c x
  let F:=FundedMarkedPathSelection.output (X x) J N y
  have v:Fin rank→Woods G coarse:=dirs x
  exact Complex.ofReal ((touch t J) (F.1 coarse a rank v))
def right (x:Cells₃):ℂ:=by
  let y:Fin 3→ Cover:=lifts R per older c x
  let F:=FundedMarkedPathSelection.output (X x) J N y
  have v:Fin rank→Woods G coarse:=dirs x
  exact Complex.ofReal ((touch t J) (plume (F.2 a rank) coarse v))
def charge (s B:ℝ):ℝ:=((priceM (Hooks G) rank s+tiePay (Hooks G) rank (s/4)+1)*B+B)*
  catchW (s/32/16) coarse

local notation "lft" => left R per Y lo older c (J:=J) X t a rank dirs
local notation "rgt" => right R per Y lo older c (J:=J) X t a rank dirs
local notation "place" => centers R per older
local notation "receipt" s:max B:max x:max => MarkU (lifts R per older c x) J
  ((row x).1 coarse a rank) ((row x).2 a rank) s B

theorem one (pin:c∈J)(s B:ℝ)(positive:0<s)(x:Cells₃)(paid:receipt s B x):
    ‖lft x-rgt x‖≤‖touch t J‖*charge R per (j:=j) rank s B*
      Real.exp (-(s/32/2)*Syn (tor coarse) (place x) J (dirs x)):=by
  have granted:=PeriodicMarkedWinding.periodized (place x) c pin positive paid
  simp only [left,right,←Complex.ofReal_sub,Complex.norm_real,←map_sub]
  rw [mul_assoc]
  exact ((touch t J).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans
    (granted.2 (dirs x))) (norm_nonneg _))

theorem original (pin:c∈J)(s B:ℝ)(positive:0<s)(r:ℝ)(φ:Test 3)
    (paid:∀x:Cells₃,weight φ (positions (R:=R) r (N,per)) x ≠ 0 → receipt s B x):
    let χ:=positions (R:=R) r (N,per)
    let W:=weight φ χ
    let bill:=‖touch t J‖*charge R per (j:=j) rank s B
    φ.applyTo (lft ∘ χ)-φ.applyTo (rgt ∘ χ) = ∑x:Cells₃,W x*(lft x-rgt x) ∧
    ‖φ.applyTo (lft ∘ χ)-φ.applyTo (rgt ∘ χ)‖≤
      ∑x:Cells₃,‖W x‖*(bill*Real.exp (-(s/32/2)*Syn (tor coarse) (place x) J (dirs x))) ∧
    ‖φ.applyTo (lft ∘ χ)-φ.applyTo (rgt ∘ χ)‖≤(∫u:Points 3,‖φ u‖)*|bill|:=by
  intro χ W bill
  have same:φ.applyTo (lft ∘ χ)-φ.applyTo (rgt ∘ χ)=∑x:Cells₃,W x*(lft x-rgt x):=by
    rw [show φ.applyTo (lft ∘ χ)=_ from tested φ χ (placed (R:=R) r (N,per)) lft,
        show φ.applyTo (rgt ∘ χ)=_ from tested φ χ (placed (R:=R) r (N,per)) rgt,←sum_sub_distrib]
    simp only [W,mul_sub]
  refine ⟨same,?_⟩
  rw [same]
  have rows:(∑x:Cells₃,‖W x*(lft x-rgt x)‖)≤
      ∑x:Cells₃,‖W x‖*(bill*Real.exp (-(s/32/2)*Syn (tor coarse) (place x) J (dirs x))):=by
    apply sum_le_sum
    intro x _
    by_cases nz:W x=0
    · simp [nz]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (one R per Y lo older c X t a rank dirs pin s B positive x (paid x nz)) (norm_nonneg _)
  have held:=(norm_sum_le ..).trans rows
  refine ⟨held,held.trans ?_⟩
  calc
    _≤∑x:Cells₃,‖W x‖*|bill|:=by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have atten:Real.exp (-(s/32/2)*Syn (tor coarse) (place x) J (dirs x))≤1:=by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        (by simpa using mul_le_mul_of_nonneg_left atten (abs_nonneg bill))
    _≤_:=by rw [←sum_mul];exact mul_le_mul_of_nonneg_right (variation φ χ (placed (R:=R) r (N,per))) (abs_nonneg _)

end YM.Integration.WilsonOriginalPublicFixedCells
end
