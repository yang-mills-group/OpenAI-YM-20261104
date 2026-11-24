import YM.Integration.WilsonTrueProjectedIntrinsic
import YM.FormalBulk08.Primer.Fields

/-! Apply the finite primary matrix to the actual filed Wilson columns.
All basis directions share one receiving vacuum and its original hard keys. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedFiledTransfer
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay PhysicalNext Repeat Legato Graces Roost
open FormalBulk08 City Pose PowerSeries Jets Orb Wick Flat Next.Free UVExtension.Free
open WilsonPhysicalMarkedDefect.RegularProjection WilsonTrueProjectedDualHistory
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D m N p i : ℕ}
local notation "𝓒" => R.family
local notation "𝓕" => R.family.labels.level d
local notation "ι" => Letter (R.family.labels.level d)
local notation "U" => transition (C:=R.family) d N p i
local notation "S" => R.family.localSection d

/-- The finite matrix is evaluated on the measured coupling at this edge. -/
def matrix (a : hue G) (wood : Primer.Families R.family) (depth : d < D)
    (N i order : ℕ) (g : ℝ) (u b : ι) : ℂ :=
  ∑ ν : Fin (order+1), ((g^ν.val * coeff ν.val (Primer.fieldStep R.family a wood depth N i u b) : ℝ) : ℂ)

def moved (A : ι → ι → ℂ) (x : ι → ℂ) : ι → ℂ := fun u => ∑ b, x b * A u b

def weighted {T X : Type*} [Fintype T] (fields : T → X → ℂ) (x : T → ℂ) (W : X) : ℂ :=
  ∑ b, x b * fields b W

abbrev submitted {X : Type*} (fields : ι → X → ℂ) (x : ι → ℂ) := weighted fields x

theorem relocated {X : Type*} (fields : ι → X → ℂ) (A : ι → ι → ℂ) (x : ι → ℂ) (W : X) :
    submitted R fields (moved R A x) W = ∑ b, x b * submitted R fields (fun u => A u b) W := by
  simp only [submitted,weighted,moved,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun u _ => mul_assoc _ _ _

private theorem push {T : Type*} [Fintype T] (fine : T → Config G ((𝓒).side (i+1) p) → ℂ) (x : T → ℂ)
    (income : ∀ b, Integrable (fine b) (prior G _)) :
    U (weighted fine x) = weighted (fun b => U (fine b)) x := by
  funext V
  let op := (𝓒).path.levels.clock.op i p
  let β := ((𝓒).path.rep N p (i+1)).beta
  let l : ℂ := ((𝓒).S.block i).val
  have integrals (b : T) : Integrable (fun W => op.density β W V • fine b W) (prior G _) :=
    StepData.push_slice ((𝓒).path.levels.transition_mass i p β) V (fine b) (income b)
  change l^d*(∫ W, op.density β W V • (∑ b, x b*fine b W) ∂prior G _) =
    ∑ b, x b*(l^d*(∫ W, op.density β W V • fine b W ∂prior G _))
  have localSum (W : Config G ((𝓒).side (i+1) p)) :
      op.density β W V • (∑ b, x b*fine b W) = ∑ b, x b • (op.density β W V • fine b W) := by
    simp only [Complex.real_smul,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _
  simp_rw [localSum]
  rw [integral_finsetSum]
  · simp_rw [integral_smul,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _
  · intro b _
    exact (integrals b).smul (x b)

/-- Sum complete signed returns on the same actual quiet representation. -/
theorem combine {T : Type*} [Fintype T] (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) {σ C Λ δ w : ℝ}
    (law : (Ψ i).Lawful σ C Λ δ w) (anchor : T) (columns : T → Spaces R p) (bills : T → ℝ)
    (receipts : ∀ b, WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (columns b) i (bills b))
    (intake : ∀ b, Integrable (columns b (i+1)) (prior G _)) (x : T → ℂ) (F : Spaces R p)
    (upper : F (i+1) = weighted (fun b => columns b (i+1)) x)
    (lower : F i = weighted (fun b => columns b i) x) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i (∑ b, ‖x b‖*bills b) := by
  choose err paid coord step using receipts
  letI : Nonempty T := ⟨anchor⟩
  let entries (b : T) := stretch (x b) (err b)
  let combined := Extra.Histories.merge (code T) entries
  have pos : 0 < safety (𝓒) i := by
    obtain ⟨_,_,_,_,_,hk,_,_⟩ := (paid anchor).2
    exact hk
  have fees (b : T) := stretch_rem (x b) (paid b).2
  have rem := (merge_budget (code T) entries pos fees (hasSum_fintype _).summable).1
  refine ⟨combined,⟨merge_format (code T) entries (fun b => stretch_format (x b) (paid b).1),?_⟩,?_,?_⟩
  · simpa only [tsum_fintype] using rem
  · change (𝓕).coeffSize (∑' b, (entries b).x) ≤ _
    rw [tsum_fintype]
    apply (Size.finite (𝓕) Finset.univ _).trans
    apply Finset.sum_le_sum
    intro b _
    change (𝓕).coeffSize (x b • (err b).x) ≤ _
    rw [Size.smul]
    exact mul_le_mul_of_nonneg_left (coord b) (norm_nonneg _)
  · rw [upper,push R _ x intake,lower]
    funext W
    have sum := (merge_density (code T) entries pos law fees (hasSum_fintype _).summable
      (hasSum_fintype _).summable S W).tsum_eq.symm
    rw [tsum_fintype] at sum
    have represented : combined.density 0 S (Ψ i) W = ∑ b, x b*(err b).density 0 S (Ψ i) W :=
      sum.trans (Finset.sum_congr rfl fun b _ => stretch_density S (Ψ i) 0 (x b) (err b) W)
    change weighted (fun b => U (columns b (i+1))) x W =
      weighted (fun b => columns b i) x W + combined.density 0 S (Ψ i) W
    rw [represented]
    simp only [weighted,step,Pi.add_apply,mul_add,Finset.sum_add_distrib]

/-- The signed return for a fitted vector costs the weighted sum of the
actual basis returns. Its compulsory part is added at each original key. -/
theorem original (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) {σ C Λ δ w : ℝ}
    (law : (Ψ i).Lawful σ C Λ δ w)
    (a : hue G) (wood : Primer.Families R.family) (depth : d < D) (order : ℕ) (g : ℝ)
    (columns : ι → Spaces R p) (basis : ι → Config G ((𝓒).side i p) → ℂ) (bills : ι → ℝ)
    (receipts : ∀ b, WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (columns b) i (bills b))
    (intake : ∀ b, Integrable (columns b (i+1)) (prior G _))
    (reused : ∀ b, columns b i = submitted R basis (fun u => matrix R a wood depth N i order g u b))
    (anchor : ι) (x : ι → ℂ) (F : Spaces R p)
    (upper : F (i+1) = submitted R (fun b => columns b (i+1)) x)
    (lower : F i = submitted R basis (moved R (matrix R a wood depth N i order g) x)) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i (∑ b, ‖x b‖*bills b) := by
  apply combine R Ψ law anchor columns bills receipts intake x F upper
  rw [lower]
  funext W
  simpa only [weighted,reused] using (relocated R basis (matrix R a wood depth N i order g) x W)

end YM.Integration.WilsonTrueProjectedFiledTransfer

