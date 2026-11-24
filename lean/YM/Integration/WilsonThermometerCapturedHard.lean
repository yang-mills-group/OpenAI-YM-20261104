import YM.Integration.WilsonThermometerRegularCofactors
import YM.Integration.WilsonThermometerCenteredAlgebra
import YM.Integration.ActualWilsonAbsoluteTransport

/-! The full signed hard/analytic remainder under the genuine older probability.
Only the positive Wilson vacuum is removed. All interacting hard summands
and all intermediate fine fields stay in the same filed numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCapturedHard
open Finset Function Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure OriginalForcedAddresses
open FVA1 WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonThermometerCourseResidual WilsonThermometerCourseIntake
open MergeProof MergeProof.East MeasureTheory Comparison.RG02 Comparison.RG02.Order
open Extraction Table Climb Trace.Pilot Next.Rank Next.UVStress ConnectedActivityE6
open IterationFour Push.AbsoluteSums.Animals OPE.Therm WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
open WilsonThermometerCenteredAlgebra
local notation "J" => Stock.census (Fin 3)

private theorem scalar (c : ℂ) (b Q : Poly J) : (total (c • b) Q).part full=c*(total b Q).part full := by
  rw [affine,affine,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => by rw [Poly.part_smul]; ring)

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {i m N per k : ℕ}
  (live : i < N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ i)
local notation "ages" => (fun j : Fin 3 => (grade j).val)
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
    order shelf seats i floor (offered R A simple live o))
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "T" => table R A simple live.le o
local notation "r" W => P.output.old.log fired W
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead disks P.model order P.voter
local notation "gr" => Coat.gStep (Ψ (i+1)).beta
local notation "lights" => rendered student (Ψ i).p gr
local notation "common" => Tint.Patrol.report student P.output gr
local notation "ν" j => scene R.family.path N per j

local notation "V" => Config G (R.family.side i per)
local notation "dose" U => ((R.family.path.rep N per i).eval U : ℂ)
local notation "Z" => (partition G (R.family.path.S.side N per) (R.family.path.β N per N) : ℂ)

/-- The complement file can be any independently proposed group-field packet on
the same representation. The forced group sum is kept until after the final
positive Wilson normalization. -/
theorem raw (E : Set V) (B : V → Poly J) (bank : Poly J) :
    let source := fun W => (total (Poly.pass (-(r W))*(T) W) bank).part full - (total (B W) bank).part full
    let hard := fun W => (Real.exp ((Ψ i).exponent W) : ℂ)*
      (total (Poly.pass ((lights).log fired W)*(common).gas fired W) bank).part full
      -(dose W)*(total (B W) bank).part full
    (∫ W,E.indicator source W ∂ν i) = (∫ W,E.indicator hard W ∂prior G (R.family.side i per))/Z := by
  intro source hard
  have point (W : V) : (dose W)*E.indicator source W=E.indicator hard W := by
    by_cases keep : W∈E
    · have left : E.indicator source W=source W := Set.indicator_of_mem keep source
      have right : E.indicator hard W=hard W := Set.indicator_of_mem keep hard
      refine (congrArg (fun z => (dose W)*z) left).trans ((?_ : (dose W)*source W=hard W).trans right.symm)
      have pos : (R.family.path.rep N per i).eval W ≠ 0 :=
        (Multi.AxisShift.chosen_positive R.makes.wilson live.le W).ne'
      have nz : (dose W) ≠ 0 := Complex.ofReal_ne_zero.mpr pos
      dsimp only [source,hard]
      rw [WilsonThermometerRegularCofactors.same R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P W,
        scalar,scalar,mul_sub,←mul_assoc (dose W) (dose W)⁻¹, mul_inv_cancel₀ nz,one_mul]
    · have left : E.indicator source W=0 := Set.indicator_of_notMem keep source
      have right : E.indicator hard W=0 := Set.indicator_of_notMem keep hard
      exact (congrArg (fun z => (dose W)*z) left).trans ((mul_zero _).trans right.symm)
  refine (OPE.Therm.violet (p:=per) R.makes.wilson live.le (E.indicator source)).trans ?_
  exact congrArg (fun z : ℂ => z/Z) (integral_congr_ae (ae_of_all _ point))

/-- Every original earlier probability hears the very same captured scalar. -/
theorem older (E : Set V) (B : V → Poly J) (bank : Poly J) {u : ℕ} (old : u ≤ i) :
    let source := fun W => (total (Poly.pass (-(r W))*(T) W) bank).part full - (total (B W) bank).part full
    let hard := fun W => (Real.exp ((Ψ i).exponent W) : ℂ)*
      (total (Poly.pass ((lights).log fired W)*(common).gas fired W) bank).part full
      -(dose W)*(total (B W) bank).part full
    Integrable (fun W => (R.family.path.rep N per i).eval W • E.indicator source W) (prior G (R.family.side i per)) →
    (∫ U,actualTransport R.family (N:=N) (E.indicator source) old U ∂ν u) =
      (∫ W,E.indicator hard W ∂prior G (R.family.side i per))/Z := by
  intro source hard paid
  exact (actualScene_transport R.family R.makes live.le paid old).trans
    (raw R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P E B bank)

end YM.Integration.WilsonThermometerCapturedHard
end
