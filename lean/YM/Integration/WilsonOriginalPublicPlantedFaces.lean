import YM.Integration.WilsonOriginalPublicPlantedLetters

/-! All occupied differences of the original planted fields and the prescribed
pivots are tested on one normalized Wilson inversion tree. Their signed values
include the change from the original sections to the public survey. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedFaces
open Function Finset PowerSeries Lattice Wilson RG Labels XSpace
open XSpace.Normalize XSpace.Cirrus XSpace.Structure1
open Maxwell Maxwell.Wick PhysicalNext.Repeat.Legato
open WilsonOriginalPublicPivotReflected (board sampled evaluated)
open WilsonOriginalPublicPivotFaces (earlier tests part)
open WilsonThermometerPositionTunedSlope (paid price finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicPlantedLetters (letter)
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (W : Initialize G) {n : ℕ} (d : Fin n → ℕ)
    (v : (i : Fin n) → (R.family.labels.level (d i)).Coeff)

def field (x : Sample n) (i : Fin n) : Bare.Series (W.tree x.F.p) G :=
  ∑b : (R.family.labels.level (d i)).Index, v i b • letter R x.F.p (W.tree x.F.p) (d i) (x.layout i) b

theorem folded (x : Sample n) (S : Finset (Fin n)) :
    board R W d v x S = Bare.normalized (W.tree x.F.p) G (∏i∈S,field R W d v x i) := by
  let h : S → ℕ := d ∘ Subtype.val
  let a : (i:S) → (R.family.labels.level (h i)).Coeff := fun i => v i
  rw [←prod_coe_sort S]
  simp_rw [field,Fintype.prod_sum]
  rw [map_sum,WilsonOriginalPublicPivotReflected.board,paid]
  apply sum_congr rfl
  intro b _
  have weights : price R h (frozen R h a) b = PowerSeries.C (∏i:S,v i (b i)) :=
    (map_prod PowerSeries.C _ univ).symm
  rw [weights,←PowerSeries.smul_eq_C_mul]
  have join : (∏i:S, v i (b i) • letter R x.F.p (W.tree x.F.p) (d i) (x.layout i) (b i)) =
      (∏i:S,v i (b i)) • ∏i:S,letter R x.F.p (W.tree x.F.p) (d i) (x.layout i) (b i) := by
    simp only [Algebra.smul_def,Finset.prod_mul_distrib,map_prod]
  rw [join,map_smul]
  exact congrArg ((∏i:S,v i (b i)) • ·)
    (WilsonOriginalPublicPlantedLetters.original R x.F.p (W.tree x.F.p) h (fun i:S=>x.layout i) b)

variable (P : (x : Sample n) → Fin n → Bare.Series (W.tree x.F.p) G)
def occupied (x : Sample n) (S B : Finset (Fin n)) : PowerSeries ℂ :=
  Bare.normalized (W.tree x.F.p) G
    ((∏i∈B,(field R W d v x i-P x i))*(∏i∈S\B,P x i))

theorem opened (x : Sample n) (S : Finset (Fin n)) :
    board R W d v x S = ∑B∈S.powerset,occupied R W d v P x S B := by
  rw [folded]
  simp only [occupied,←map_sum,←Finset.prod_add,sub_add_cancel]

variable {L : Type*} [Fintype L] (X : L → Sample n) (μ : L → ℂ) (q : ℕ) (g : ℝ)

private def evaluator (q : ℕ) (g : ℝ) : PowerSeries ℂ →ₗ[ℂ] ℂ :=
  ∑k∈Finset.Iic q,(g:ℂ)^k • (coeff (R:=ℂ) k)
private theorem evaluates (y : PowerSeries ℂ) : evaluator q g y = evaluated q g y := by
  simp only [evaluator,evaluated,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

theorem tested (S : Finset (Fin n)) :
    sampled R W d v X μ S q g - tests X μ q g (fun x=>part R W d v P x S ∅) =
      ∑B∈S.powerset.erase ∅, tests X μ q g (fun x=>occupied R W d v P x S B) := by
  have one (l:L) : μ l*evaluated q g (board R W d v (X l) S) =
      μ l*evaluated q g (part R W d v P (X l) S ∅) +
      ∑B∈S.powerset.erase ∅,μ l*evaluated q g (occupied R W d v P (X l) S B) := by
    have nil : occupied R W d v P (X l) S ∅ = part R W d v P (X l) S ∅ := by
      simp [occupied,WilsonOriginalPublicPivotFaces.part]
    calc
      _ = ∑B∈S.powerset,μ l*evaluated q g (occupied R W d v P (X l) S B) := by
        rw [opened R W d v P (X l) S,←evaluates,map_sum,Finset.mul_sum]
        simp only [evaluates]
      _ = μ l*evaluated q g (occupied R W d v P (X l) S ∅) +
          ∑B∈S.powerset.erase ∅,μ l*evaluated q g (occupied R W d v P (X l) S B) :=
        (Finset.add_sum_erase S.powerset _ (mem_powerset.mpr (empty_subset S))).symm
      _ = _ := by rw [nil]
  simp only [sampled,tests,one,Finset.sum_add_distrib,add_sub_cancel_left]
  exact Finset.sum_comm

def share (S B : Finset (Fin n)) : ℂ :=
  tests X μ q g (fun x=>occupied R W d v P x S B) -
    tests X μ q g (fun x=>part R W d v P x S B)

theorem original (S : Finset (Fin n)) :
    tests X μ q g (fun x=>earlier R W d v x S) =
        ∑B∈S.powerset.erase ∅,share R W d v P X μ q g S B ∧
    ∀ B, share R W d v P X μ q g S B + tests X μ q g (fun x=>part R W d v P x S B) =
        tests X μ q g (fun x=>occupied R W d v P x S B) := by
  constructor
  · have earlierSum := WilsonOriginalPublicPivotFaces.split R W d v P X μ q g S
    rw [tested R W d v P X μ q g S] at earlierSum
    simp only [share,Finset.sum_sub_distrib]
    exact eq_sub_of_add_eq earlierSum.symm
  · intro B
    exact sub_add_cancel _ _

end YM.Integration.WilsonOriginalPublicPlantedFaces
