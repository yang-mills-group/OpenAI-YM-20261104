import YM.Integration.WilsonOriginalDepositedHard
import YM.MergeProof.Pitch
import YM.QuadraticLocal.Germ.Stock

/-! Recover the complete physical singleton from each admissible inventory and its funded sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedHardTable
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Overlay QuadraticLocal QuadraticLocal.Affinity
open QuadraticLocal.Fusion.Attached MergeProof.Accent WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (prior : Hard T P.p P.activities.forced P.activities.K o J) (j : V)
  (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ)

theorem inventory [Fintype V] (x : T) (U : Config G n) (I : Finset ℕ) :
    (packet P.activities P.p ((joined prior j q law t).hard x) U I).part (J.fire j) -
    (packet P.activities P.p (prior.hard x) U I).part (J.fire j) = t x*q.marked P I U := by
  unfold packet Coefficient.marked
  split
  next =>
    simp only [shockProd,Hard.quiet,WilsonOriginalDepositedHard.posted,Poly.part_plus,Poly.part_send,if_neg (J.fire_hot j).symm,add_zero,↓reduceIte]
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
    congr 3
    exact Subsingleton.elim _ _
  next => simp

theorem full [Fintype V] (w : V → ℝ) (hw : ∀ i, 0 < w i) {κ B k : ℝ}
    (base : prior.Paid w P.p.B P.p.supportExponent k) (tested : ∀ x, ‖t x‖ ≤ 1)
    (actual : q.remBound (o j) P κ B) (x : T) (U : Config G n) :
    (∑' i, packet P.activities P.p ((joined prior j q law t).hard x) U i).part (J.fire j) -
    (∑' i, packet P.activities P.p (prior.hard x) U i).part (J.fire j) =
        t x * ∑' i, q.marked P i U := by
  have h₀ := Hard.packet_summing prior base P.p.exponent_pos.le hw x U
  have h₁ := Hard.packet_summing _ (paid prior j q law t w hw base tested actual) P.p.exponent_pos.le hw x U
  let a := packet P.activities P.p ((joined prior j q law t).hard x) U
  let b := packet P.activities P.p (prior.hard x) U
  change (∑' i, a i).part (J.fire j) - (∑' i, b i).part (J.fire j) = _
  calc _ = (tsum (fun i : Finset ℕ => a i - b i)).part (J.fire j) := by rw [h₁.tsum_sub h₀]; rfl
       _ = ∑' i, t x*q.marked P i U := (Poly.share (h₁.sub h₀) _).trans
              (tsum_congr fun i => inventory prior j q law t x U i)
       _ = _ := tsum_mul_left

section
variable {Y : V → Type} [∀i, AddCommGroup (Y i)]
  {𝕜 : Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] [∀i, Module 𝕜 (Y i)]
  (C : ∀i, Set (Y i)) (K : ∀i, Submodule 𝕜 (Y i))
  (old : Hard (Wallet C) P.p P.activities.forced P.activities.K o J)
  (a : Wallet C → ℂ)
theorem crown (h₀ : Crown (fun v => {o v}) C K old) (h₁ : Attn K C {j} a) :
    Crown (fun v => {o v}) C K (joined old j q law a) := by
  constructor
  intro i U
  apply (h₀.lesson i U).sum
  constructor
  intro s
  by_cases hs : s=J.fire j
  · subst s
    simp only [Poly.part_send,↓reduceIte]
    constructor
    · simpa [Census.fire] using h₁.bind (Attn.solid (K:=K) (A:=C) (q.forced i U))
          (show Disjoint ({j} : Finset V) ∅ by simp)
    · intro x hn v hv
      have hvj : v=j := Finset.mem_singleton.mp hv
      subst v
      exact Finset.singleton_subset_iff.mpr (law.carried i (fun h => hn (by simp [h])))
  · simp only [Poly.part_send,if_neg hs]
    exact Addressable.gone
end

end YM.Integration.WilsonOriginalDepositedHardTable
