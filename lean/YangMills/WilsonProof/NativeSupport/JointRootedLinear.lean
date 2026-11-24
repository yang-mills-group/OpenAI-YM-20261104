import YangMills.WilsonProof.NativeSupport.JointOwnerTally
import YangMills.WilsonProof.NativeSupport.JointMountedTariff

/-! Sum the original one-switch RollsUp price over an arbitrary set of
output modes. A mode is charged once to its source even when the source
is represented in a much larger numerical campaign or has many names. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Finset Lattice RG Wilson Marker MergeProof MergeProof.Menu
open FullVolume.Ray PhysicalNext.Repeat PhysicalNext.Repeat.Luna
open scoped BigOperators Classical
variable {I J V : Type} [Fintype I] [Fintype J] [DecidableEq V] {B : Census V}
variable {G : Gauge} {f c : Side} {R : Rep G f}
variable (q : I  →  Hat B R) (v : V → ℝ) (hv : ∀ x,0<v x)
variable (P : BudgetPoint) (X : J → Support c) (F : I → sun → J → Config G c → ℂ) (e r τ : ℝ)
variable (paid : ∀ i, RollsUp P X (F i) r e (τ*(‖((sumFee (q i) v:ℝ):ℂ)‖*load (q i).M)))

include hv paid in
theorem linear_modes :
    ∃ cap : J  →  B.Mode  →  ℝ, (∀ j p,0 ≤ cap j p) ∧
      (∀ (s : sun) (j : J) (U : Config G c) (p : B.Mode),‖∑ i,F i s j U*(sing (q i) v).part p‖ ≤ cap j p) ∧
      ∀ (w : V → ℝ), (∀ x,0<w x)  →  ∀ D : Finset B.Mode,
        (∑ j,Real.exp (e*coverNumber P.B (X j))*
          ∑ p∈D,Poly.toll w p*cap j p) ≤
        τ*∑ i : I with (q i).s∈D, sumFee (q i) w*load (q i).M := by
  choose a brill rate using fun i=>(paid i).funds
  let L (j:J) := Real.exp (e*coverNumber P.B (X j))
  let c₀ (i:I) (p:B.Mode) := ‖(sing (q i) v).part p‖
  let A (j:J) (p:B.Mode) := ∑ i,a i j*c₀ i p
  have pos (i:I) (j:J) : 0 ≤ a i j := (rate i j (1:Config G c)).nonneg
  have bound (s:sun) (i:I) (j:J) (U:Config G c) : ‖F i s j U‖≤ a i j := by
    simpa only [Jams.phraseS,Jams.pinch_eq] using (rate i j U).held s.property
  refine ⟨A,fun j p=>sum_nonneg fun i _=>mul_nonneg (pos i j) (norm_nonneg _),?_,?_⟩
  · intro s j U p
    exact (norm_sum_le _ _).trans (sum_le_sum fun i _=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (bound s i j U) (norm_nonneg _))
  intro w hw D
  let cost (i:I) := ∑ p∈D,Poly.toll w p*c₀ i p
  have nc (i:I) : 0 ≤ cost i := sum_nonneg fun p _=>mul_nonneg (Poly.worth hw p).le (norm_nonneg _)
  have per (j:J) : (∑ p∈D,Poly.toll w p*A j p)=∑ i,cost i*a i j := by
    unfold A cost
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun i _=>sum_congr rfl fun p _=>by ring
  have src (i:I) : cost i*‖((sumFee (q i) v:ℝ):ℂ)‖ =
      if (q i).s∈D then sumFee (q i) w else 0 := by
    have normalize (p:B.Mode) : c₀ i p*‖((sumFee (q i) v:ℝ):ℂ)‖=‖(stamp (q i)).part p‖ := by
      rw [mul_comm,←norm_mul,←Poly.part_smul,Menu.purchase (q i) hv]
    unfold cost
    simp_rw [sum_mul,mul_assoc,normalize,Menu.stamp,Poly.part_send]
    simp only [apply_ite norm,norm_zero,mul_ite,mul_zero,sum_ite_eq',Menu.sumFee]
  change (∑ j,L j*(∑ p∈D,Poly.toll w p*A j p)) ≤ _
  calc _ = ∑ i,cost i*(∑ j,L j*a i j) := by
            simp_rw [per,Finset.mul_sum]
            rw [sum_comm]
            exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring
       _ ≤ ∑ i,cost i*(τ*(‖((sumFee (q i) v:ℝ):ℂ)‖*load (q i).M)) :=
            sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap (brill i) univ) (nc i)
       _ = _ := by
            rw [mul_sum,sum_filter]
            apply sum_congr rfl
            intro i _
            rw [show cost i*(τ*(‖((sumFee (q i) v:ℝ):ℂ)‖*load (q i).M))=
                τ*((cost i*‖((sumFee (q i) v:ℝ):ℂ)‖)*load (q i).M) by ring,src]
            split <;> simp

end YM.Integration.InletSusceptibility.NativeSwitch
