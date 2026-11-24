import YM.Integration.WilsonSurveyedColorVacuumPublic
import YM.Integration.WilsonSurveyedColorVacuumBasis

/-! The same orthogonal color operation at every perturbative order of the
actual smeared MS kernel, on the full cumulative complex physical quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumKernel
open Function Finset PowerSeries Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Dframe FVA2.Scale FVA2.Scale.Equator FVA2.Scale.Jury
open FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Read FVA2.Position.OpenAxis
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open WilsonSurveyedColorOpenIndex WilsonSurveyedColorCurvature WilsonSurveyedColorNormalizers
open WilsonSurveyedColorAppointed WilsonSurveyedColorVacuumBasis
open scoped Classical BigOperators Matrix
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ) {d n : ℕ}
local notation "N" => groupAction hG U same
local notation "R" => wave a M

omit [PreconnectedSpace G.El] in
private theorem leg (k : ℕ) (x : Points n) (hx : x ∈ conf n) (p : Scan G n) (hp : Guarded p d) :
    coeff k (install R n x p) = fxt (R d) x k (tape p hp) := by
  rw [caring p hp (regular_wave a M) hx]
  simp only [test,Reg.Point.story,coeff_mk,fxt,dif_pos hx]

theorem basis (k : ℕ) (x : Points n) (hx : x ∈ conf n) (p : Scan G n) (hp : Guarded p d) :
    fxt (R d) x k (fun i => axis U N d (tape p hp i)) = fxt (R d) x k (tape p hp) := by
  have h := congrArg (fun K : Album G => coeff k (K n x p))
    (WilsonSurveyedColorVacuumPublic.invariant hG U same M a)
  change coeff k (concert (chart U N) p (install R n x)) = coeff k (install R n x p) at h
  rw [coefficient,leg M a k x hx p hp] at h
  rw [expand]
  convert h using 1
  apply sum_congr rfl
  intro v _
  rw [leg M a k x hx (decode p v) (readyP hp v)]

theorem point (k : ℕ) (x : Points n) (hx : x ∈ conf n) (v : Tags G d n) :
    fxt (R d) x k (fun i => axis U N d (v i)) = fxt (R d) x k v := by
  let P := fxt (R d) x k
  let Z := P.compLinearMap (fun _ => axis U N d)
  change Z v = P v
  rw [stencil_he Z v,stencil_he P v]
  apply sum_congr rfl
  intro w _
  congr 1
  exact basis hG U same M a k x hx (flash ∘ w) (fun i => size_le (w i))

theorem tested (d k : ℕ) :
    recruit (axis U N d) (Reg.State.kernel a M d k) = Reg.State.kernel a M d k := by
  ext1 n
  ext1 t
  ext1 v
  change Reg.State.kernel a M d k n t (fun i => axis U N d (v i)) =
    Reg.State.kernel a M d k n t v
  rw [(initial a M).exact,(initial a M).exact]
  apply Test.apply_eq
  intro x hx
  exact point hG U same M a k x hx v

end YM.Integration.WilsonSurveyedColorVacuumKernel
end
