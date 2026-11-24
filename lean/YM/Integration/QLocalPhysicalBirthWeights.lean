import YM.Integration.QLocalPhysicalBirthInvoice

/-! One positive startup radius is fixed before the cutoff, period, origins,
configuration and tests. The chosen label and cover ceiling are paid at their
original scale, with the genuine mandatory gas on the physical clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthWeights
open Function Filter Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums
open scoped BigOperators Classical Topology

private theorem scaled {V : Type*} [Fintype V] {n : Side} (X : V → Support n) (B : ℕ)
    (f F : V → ℝ) (a r : ℝ) (hr : 0 < r) (hf : ∀ i, 0 ≤ f i) (hF : ∀ i, 0 ≤ F i)
    (h : ∀ i, f i * Real.exp (a * coverNumber B (X i)) ≤ F i) :
    Ac.Hit X B (fun i => (r/(1+∑ j, F j))*f i) a r := by
  have hS : 0 ≤ ∑ j, F j := Finset.sum_nonneg fun j _ => hF j
  have hden : 0 < 1+∑ j, F j := by linarith
  let W := r/(1+∑ j, F j)
  have hW : 0 ≤ W := (div_pos hr hden).le
  intro x
  refine ⟨fun i => ite_nonneg (mul_nonneg (mul_nonneg hW (hf i)) (Real.exp_nonneg _)) le_rfl,
    Summable.of_finite, ?_⟩
  rw [tsum_fintype]
  calc ∑ i, (if x ∈ X i then W*f i*Real.exp (a * coverNumber B (X i)) else 0) ≤ ∑ i, W * F i := by
          apply Finset.sum_le_sum
          intro i _
          split
          · rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (h i) hW
          · exact mul_nonneg hW (hF i)
       _ = W*(∑ i, F i) := (Finset.mul_sum ..).symm
       _ ≤ W*(1+∑ i, F i) := mul_le_mul_of_nonneg_left (by linarith) hW
       _ = r := div_mul_cancel₀ r hden.ne'

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (L : ℕ)
  (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.levels.budget L
local notation "u₀" => fun i => ActualRunUnmaskedPartners.globalPrice R L 0 L (d i) (v i)
local notation "c₀" => fun i => ActualRunPhysicalPages.price R L (d i) (v i)

def exposure (C : ℝ) (i : V) : ℝ := ((u₀) i + (c₀) i) * Real.exp ((P₀).supportExponent*C)

def weight (C r : ℝ) (_ : V) : ℝ := r/(1+∑ i, exposure R L d v C i)

omit [DecidableEq V] [Fintype V] in
private theorem costs (href : ∀ i, R.family.ref (d i) ≤ L) :
    (∀ i, 0 ≤ (u₀) i) ∧ ∀ i, 0 ≤ (c₀) i := by
  refine ⟨fun i => (norm_nonneg _).trans (ActualRunUnmaskedPartners.kernel_global R L 0 L (d i) (v i) 0 1), ?_⟩
  intro i
  exact (ActualRunPhysicalPages.priced R L 0 L (d i) le_rfl (href i) (v i) 0).2.1

omit [DecidableEq V] in
theorem positive (C : ℝ) {r : ℝ} (hr : 0 < r) (href : ∀ i, R.family.ref (d i) ≤ L) (i : V) :
    0 < weight R L d v C r i := by
  have h := costs R L d v href
  apply div_pos hr
  have hs : 0 ≤ ∑ j, exposure R L d v C j := Finset.sum_nonneg fun j _ =>
    mul_nonneg (add_nonneg (h.1 j) (h.2 j)) (Real.exp_nonneg _)
  linarith

theorem charges (N p : ℕ) (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L)
    (o : Positions V (R.family.side L p)) {a C r : ℝ} (hr : 0 < r) (ha : a ≤ (P₀).supportExponent)
    (hC : ∀ i, (coverNumber (P₀).B (ActualRunPhysicalPages.cover R p L (d i) o i) : ℝ) ≤ C) :
    let X := fun i => ActualRunPhysicalPages.cover R p L (d i) o i
    let W := weight R L d v C r
    Ac.Hit X (R.family.path.rep N p L).p.B (fun i => W i *
      ActualRunUnmaskedPartners.globalPrice R N p L (d i) (v i)) a r ∧
    Ac.Hit X (R.family.path.rep N p L).p.B (fun i =>
      (ActualRunPhysicalPages.page R N p L (d i) o i (v i) (B := Ribbon.Bud V)).due W ((c₀) i)) a r := by
  dsimp only
  let X := fun i => ActualRunPhysicalPages.cover R p L (d i) o i
  have hp : (R.family.path.rep N p L).p = (P₀) := (R.makes.wilson.represents N p L hL).vac
  have hb : (R.family.path.rep L 0 L).p = (P₀) := (R.makes.wilson.represents L 0 L le_rfl).vac
  have hu (i : V) : ActualRunUnmaskedPartners.globalPrice R N p L (d i) (v i) = (u₀) i := by
    simp only [ActualRunUnmaskedPartners.globalPrice,hp,hb]
  have H := costs R L d v href
  have hF (i : V) : 0 ≤ exposure R L d v C i := mul_nonneg (add_nonneg (H.1 i) (H.2 i)) (Real.exp_nonneg _)
  have e (i : V) : Real.exp (a*coverNumber (P₀).B (X i)) ≤ Real.exp ((P₀).supportExponent*C) := by
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hC i) (P₀).exponent_pos.le))
  have U := scaled X (P₀).B (u₀) (exposure R L d v C) a r hr H.1 hF (fun i =>
    mul_le_mul (by linarith [H.2 i] : (u₀) i ≤ (u₀) i + (c₀) i) (e i) (Real.exp_nonneg _) (add_nonneg (H.1 i) (H.2 i)))
  have W := scaled X (P₀).B (c₀) (exposure R L d v C) a r hr H.2 hF (fun i =>
    mul_le_mul (by linarith [H.1 i] : (c₀) i ≤ (u₀) i + (c₀) i) (e i) (Real.exp_nonneg _) (add_nonneg (H.1 i) (H.2 i)))
  constructor
  · simpa only [hp,hu,weight] using U
  · simpa [hp,ActualRunPhysicalPages.page,Page.due,Poly.toll,Census.fire,weight] using W

end YM.Integration.QLocalPhysicalBirthWeights
end
