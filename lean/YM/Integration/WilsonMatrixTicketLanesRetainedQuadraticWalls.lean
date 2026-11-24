import YM.Integration.WilsonMatrixTicketLanesRetainedCrossed
import YM.Integration.WilsonMatrixTicketLanesRetainedCurls

/-! Spatial decay of the measured first non-scalar conditional Wick response with both means kept. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticWalls
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open PertExtension PertExtension.GaussianScore RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven RGComparison.Core16.Spool
open RGComparison.Core16.Silk FVA2.CityHistory WilsonMatrixTicketLanesReportedWords WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesRetainedAngular WilsonMatrixTicketLanesRetainedCrossed
open WilsonMatrixTicketLanesRetainedCurls
open scoped Topology BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "Dual" => Module.Dual ℝ E


private def first (Γ : Law E) (b c d : Module.Dual ℝ E) (s : E) : Dual→ₗ[ℝ]ℝ where
  toFun z:=cross Γ z b c d s
  map_add' x y:=by simp [cross,Law.wick];ring
  map_smul' t x:=by simp [cross,Law.wick,smul_eq_mul];ring
private def second (Γ : Law E) (a c d : Module.Dual ℝ E) (s : E) : Dual→ₗ[ℝ]ℝ where
  toFun z:=cross Γ a z c d s
  map_add' x y:=by simp [cross,Law.wick];ring
  map_smul' t x:=by simp [cross,Law.wick,smul_eq_mul];ring
private def third (Γ : Law E) (a b d : Module.Dual ℝ E) (s : E) : Dual→ₗ[ℝ]ℝ where
  toFun z:=cross Γ a b z d s
  map_add' x y:=by simp [cross,Law.wick];ring
  map_smul' t x:=by simp [cross,Law.wick,smul_eq_mul];ring
private def fourth (Γ : Law E) (a b c : Module.Dual ℝ E) (s : E) : Dual→ₗ[ℝ]ℝ where
  toFun z:=cross Γ a b c z s
  map_add' x y:=by simp [cross,Law.wick];ring
  map_smul' t x:=by simp [cross,Law.wick,smul_eq_mul];ring

omit [FiniteDimensional ℝ E] in
private theorem triangle (L : Dual→ₗ[ℝ]ℝ) (e : Fin 4→Dual) {B : ℝ} (price : ∀i,|L (e i)|≤B) :
    |L (∑i,orientation i • e i)|≤4*B := by
  have sign (i : Fin 4) : |orientation i|=1:=by fin_cases i <;> norm_num [orientation]
  rw [map_sum]
  calc _ ≤ ∑i,|L (orientation i • e i)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : Fin 4,B := Finset.sum_le_sum (fun i _=>by simpa only [map_smul,smul_eq_mul,abs_mul,sign,one_mul] using price i)
       _ = _ := by simp

variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Forest S.ratio)
local notation "V" => Future G S T

/-- The estimate requires four actual plaquette corners per tested color. There is no volume factor. -/
theorem plaquettes (Γ : Law V) (s : V) (a b c d : Face (Per f)) (e g h j : G.ColorIndex) {B : ℝ}
    (price : ∀ i k m n : Fin 4, |cross Γ (wire S T (corners a i) e) (wire S T (corners b k) g)
      (wire S T (corners c m) h) (wire S T (corners d n) j) s|≤B) :
    |cross Γ (curl S T a e) (curl S T b g) (curl S T c h) (curl S T d j) s|≤256*B := by
  let A:=fun i=>wire S T (corners a i) e
  let C:=fun i=>wire S T (corners b i) g
  let D:=fun i=>wire S T (corners c i) h
  let H:=fun i=>wire S T (corners d i) j
  have n₃ (i k m) : |cross Γ (A i) (C k) (D m) (curl S T d j) s|≤4*B := by
    rw [placed];exact triangle (fourth Γ (A i) (C k) (D m) s) H (price i k m)
  have n₂ (i k) : |cross Γ (A i) (C k) (curl S T c h) (curl S T d j) s|≤4*(4*B) := by
    rw [placed S T c h];exact triangle (third Γ (A i) (C k) (curl S T d j) s) D (n₃ i k)
  have n₁ i : |cross Γ (A i) (curl S T b g) (curl S T c h) (curl S T d j) s|≤4*(4*(4*B)) := by
    rw [placed S T b g];exact triangle (second Γ (A i) (curl S T c h) (curl S T d j) s) C (n₂ i)
  rw [placed S T a e,show (256:ℝ)*B=4*(4*(4*(4*B))) from by ring]
  exact triangle (first Γ (curl S T b g) (curl S T c h) (curl S T d j) s) A n₁

/-- The original finite-torus distance is measured on all entered fine links. -/
def clear (a b c d : Face (Per f)) (H : ℕ) := ∀z∈[c,d],∀y∈[a,b],∀i j : Fin 4,
  H≤Lattice.separation (corners z i).1 (corners y j).1

end YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticWalls
