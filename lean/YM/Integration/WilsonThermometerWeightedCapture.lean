import YM.Integration.WilsonThermometerCapturedHard
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! The complete horizon-zero original cutoff table is returned as one signed
formatted coefficient on its true underlying Wilson representation. The forced
payloads are added at their actual, already occupied compulsory addresses. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWeightedCapture
open Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Marker QuadraticLocal
open FVA1 PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation
open WilsonThermometerCourseIntake WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {N per i : ℕ} (upper : i ≤ N) (o : Positions (Fin 3) (R.family.side N per))
local notation "frame₀" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "data" U => incoming R A simple upper o U
local notation "V" => Config G (R.family.side i per)
local instance : Nonempty ((J).Mode) := ⟨(J).quiet⟩

def assembled {d : ℕ} {F : Frame G d} {n : Side} (H : (J).Mode → Coefficient F n) (Q : Poly J) :
    Coefficient F n := merge (code ((J).Mode)) (fun s => stretch (weight Q s) (H s))

/-- Each same-anchor entry can already contain legitimate old forced
payloads and its own full conditional regular density. -/
theorem deposited (post : Rep G (R.family.side i per)) (y : Site (R.family.side i per)) (H : (J).Mode → Coefficient (frame₀) (R.family.side i per))
    (Q : Poly J) {κ σ c Λ δ ℓ : ℝ} (hp : 0 < κ) (law : post.Lawful σ c Λ δ ℓ)
    (fare : (J).Mode → ℝ) (fit : ∀ s,(H s).Format y (Y) post)
    (paid : ∀ s,(H s).remBound y post κ (fare s))
    (issued : ∀ s (U : V),(H s).density y (S) post U=((data U).part s)) :
    let D:=assembled H Q
    D.Format y (Y) post ∧ D.remBound y post κ (∑ s,‖weight Q s‖*fare s) ∧
    D.x=∑ s,weight Q s • (H s).x ∧
    (∀ j (U : V),D.forced j U=∑ s,weight Q s*(H s).forced j U) ∧
    ∀ U : V,D.density y (S) post U=(total (data U) Q).part full := by
  intro D
  let pieces (s : (J).Mode) := stretch (weight Q s) (H s)
  have raw (s : (J).Mode) : (pieces s).remBound y post κ (‖weight Q s‖*fare s) := stretch_rem _ (paid s)
  have formats := merge_format (code ((J).Mode)) pieces (fun s=>stretch_format _ (fit s))
  have tariff := (merge_budget (code ((J).Mode)) pieces hp raw (hasSum_fintype _).summable).1
  refine ⟨formats,by simpa only [D,assembled,pieces,tsum_fintype] using tariff,tsum_fintype _,?_,?_⟩
  · intro j U
    exact tsum_fintype _
  · intro U
    have sum := merge_density (code ((J).Mode)) pieces hp law raw (hasSum_fintype _).summable
      (hasSum_fintype _).summable (S) U
    change (merge _ pieces).density _ _ _ _=_
    rw [← sum.tsum_eq,tsum_fintype,WilsonThermometerCenteredAlgebra.affine]
    exact sum_congr rfl fun s _ => (stretch_density (S) post y _ (H s) U).trans (congrArg (weight Q s*·) (issued s U))

/-- Charge a common actual finite-member gross bill once using the complete
finite coefficient inverse. The signed coordinate and the forced invoices
are booked in the very same radius. -/
theorem price {d : ℕ} {F : Frame G d} {n : Side} (H : (J).Mode → Coefficient F n) (Q : Poly J)
    (fare : (J).Mode → ℝ) {g allowance gross : ℝ} (gp : 0 ≤ g) (ncap power : ℕ)
    (fee : g^ncap*(∑ s : (J).Mode,‖weight Q s‖) ≤ allowance)
    (bound : ∀ s, g^power*fare s ≤ gross ∧ g^power*F.coeffSize (H s).x ≤ gross) (good : 0 ≤ gross) :
    g^(ncap+power)*(∑ s,‖weight Q s‖*fare s) ≤ allowance*gross ∧
    g^(ncap+power)*F.coeffSize (assembled H Q).x ≤ allowance*gross := by
  have spend (f : (J).Mode → ℝ) (h : ∀s,g^power*f s ≤ gross) :
      g^(ncap+power)*(∑ s,‖weight Q s‖*f s) ≤ allowance*gross := by
    rw [pow_add,mul_assoc,Finset.mul_sum]
    calc
      _ ≤ g^ncap*(∑ s,‖weight Q s‖*gross) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg gp _)
        exact sum_le_sum fun s _=>by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (h s) (norm_nonneg _)
      _ = (g^ncap*(∑ s,‖weight Q s‖))*gross := by rw [←Finset.sum_mul,mul_assoc]
      _ ≤ allowance*gross := mul_le_mul_of_nonneg_right fee good
  refine ⟨spend _ (fun s=>(bound s).1),?_⟩
  have line : (assembled H Q).x=∑ s,weight Q s • (H s).x := tsum_fintype _
  rw [line]
  have grossX := Size.finite F univ (fun s=>weight Q s • (H s).x)
  apply (mul_le_mul_of_nonneg_left grossX (pow_nonneg gp _)).trans
  simpa only [Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,←Finset.mul_sum] using
    (spend (fun s=>F.coeffSize (H s).x) (fun s=>(bound s).2))

end YM.Integration.WilsonThermometerWeightedCapture
end
