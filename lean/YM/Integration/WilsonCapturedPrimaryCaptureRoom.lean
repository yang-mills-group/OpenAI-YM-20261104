import YM.Integration.WilsonCapturedPrimaryCompactSites
import YM.Integration.WilsonCapturedPrimaryTrailSites

/-! The reporting halo opens for the actual compact shape on the original
dated trajectory, simultaneously at every supported placement and finite regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCaptureRoom
open Filter Finset Lattice Wilson RG Source Marker Extraction Cells RG12 QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato FVA1 ActualRunUnmaskedPartners
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G)

theorem shape (φ : Test 3) :
    ∃ K:ℕ,∀ x:Points 3,φ x ≠ 0 → ∀ v a,|x v a| ≤ (K:ℝ) := by
  let f (x : Points 3) := ∑ v:Fin 3,∑ a:Axis, |x v a|
  have smooth : Continuous f := by dsimp only [f];fun_prop
  obtain ⟨B,supremum⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn smooth.continuousOn
  refine ⟨⌈B⌉₊,?_⟩
  intro x hx v a
  have mem : x ∈ tsupport (fun x=>φ x) := subset_closure hx
  have positive (v:Fin 3) (a:Axis): 0 ≤ |x v a| := abs_nonneg _
  calc
    |x v a| ≤ ∑ b:Axis,|x v b| := single_le_sum (fun b _=>positive v b) (mem_univ a)
    _ ≤ f x := single_le_sum
      (f:=fun w:Fin 3=>∑b:Axis,|x w b|) (fun w _=>sum_nonneg (fun b _=>positive w b)) (mem_univ v)
    _ ≤ ‖f x‖ := le_abs_self _
    _ ≤ B := supremum x mem
    _ ≤ _ := Nat.le_ceil _

theorem capture (simple : G.Simple) (φ : Test 3) :
    ∀ᶠ i:ℕ in atTop,∀ (r:ℝ), |r| ≤ R.family.S.a i →
      ∀ (N per : ℕ) (live : i ≤ N) (o : Fin 3 → Site (R.family.side N per)),
        WilsonSeparatedOriginalThermometerCells.weight φ
          (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)) o ≠ 0 →
        ∀v, separation ((R.family.S.toDepth live per).parent (o v)) 0 ≤ (R.family.path.levels.budget i).B := by
  obtain ⟨K,bound⟩:=shape φ
  have rise:=Multi.Wage.ranges simple R.family.path.levels
  filter_upwards [rise.eventually_ge_atTop (K+2)] with i large
  intro r paid N per live o active v
  apply (WilsonCapturedPrimaryCompactSites.original R φ r (N,per) live (K+1) o ?_ active v).trans large
  intro x hx t a
  change |r*x t a|+R.family.S.a i ≤ ((K+1:ℕ):ℝ)*R.family.S.a i
  rw [abs_mul,Nat.cast_succ,add_mul,one_mul]
  exact add_le_add ((mul_le_mul paid (bound x hx t a) (abs_nonneg _) (R.family.S.a_pos i).le).trans_eq
    (mul_comm _ _)) le_rfl

end YM.Integration.WilsonCapturedPrimaryCaptureRoom
