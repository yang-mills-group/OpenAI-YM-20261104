import YM.Integration.SelectedCofactorCommonVacuum

/-! The native support mass pays one common all-mode bill across every
independent test and field. It retains the actual unmarked rows separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorSupportBudget
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison RG3.Forms RG3.Script.Picnic Push.AbsoluteSums
open NativeTasteCoveredCofactor SectorNext.Vacuum MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p pK : BudgetPoint} {w cost : V → ℝ}
    {κ reg fro vacuum : ℝ}

/-- Every marked physical row sum converges before taking any signed detector. -/
theorem tagged_summable (h : RelativeBudget p T w κ (envelopeProduct cost) reg fro)
    (hc : ∀v, 0 < cost v) (x : X) (i : ℕ) (U : Config G n) :
    Summable (fun j => (T.leaf x).contents.tagged i j U) := by
  have hs := ((towed_restoreEnvelope cost hc (h.budget.native_marked x)).repair
    (relativeRadii_positive h.budget.radii hc) (x,U)).2
  have hj := hs.comp_injective (i := fun j : ℕ => (i,j)) (fun _ _ he => congrArg Prod.snd he)
  exact hj.congr (fun j => restoreEnvelope_send _ _ _ _)

private theorem full_rows (h : FullBudget p T w κ reg fro) (x₀ : X) :
    ∃ m : ℕ → ℝ, (∀ i, 0 ≤ m i) ∧
      SumBudget (fun i => p.mass (P.activities.forced i).support (m i)) (Fintype.card V * (κ * fro)) ∧
      ∀ x U i, Poly.price w ((T.leaf x).contents.each i U - scalarRow P U i) ≤ m i := by
  let d i := Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)
  let q (a : ℕ × ℕ) := Poly.toll w (T.menu.marks a.1 a.2) * p.mass (P.activities.forced a.1).support (h.black a)
  have hq0 a : 0 ≤ q a := mul_nonneg (Poly.worth h.radii _).le (mul_nonneg (Real.exp_pos _).le (h.black_nonnegative a))
  have hq : SumBudget q (Fintype.card V * (κ * fro)) := Overlay.per_system hq0
    (fun a : ℕ × ℕ => (h.active x₀).articles.occurs a.1 a.2) h.forcedTotal
  obtain ⟨hf,ho⟩ := (summable_prod_of_nonneg (show 0 ≤ q from hq0)).mp hq.2.1
  let b i := ∑' j, q (i,j)
  let m i := (d i)⁻¹ * b i
  have hd i : 0 < d i := Real.exp_pos _
  have hmass i : p.mass (P.activities.forced i).support (m i) = b i := by
    change d i * ((d i)⁻¹ * b i) = b i
    rw [mul_inv_cancel_left₀ (hd i).ne']
  refine ⟨m, fun i => mul_nonneg (inv_nonneg.mpr (hd i).le) (tsum_nonneg fun j => hq0 (i,j)), ?_, ?_⟩
  · simp_rw [hmass]
    exact ⟨fun i => tsum_nonneg fun j => hq0 (i,j), ho, (hq.2.1.tsum_prod).symm.trans_le hq.2.2⟩
  intro x U i
  change Poly.price w ((Poly.bead R (P.activities.K i U : ℂ) + ∑' j, (T.leaf x).contents.tagged i j U) - Poly.bead R _) ≤ m i
  rw [add_sub_cancel_left]
  have ht j : Poly.price w ((T.leaf x).contents.tagged i j U) ≤ (d i)⁻¹ * q (i,j) := by
    change Poly.price w (Poly.send (T.menu.marks i j) (T.menu.force x i j U)) ≤ _
    rw [Poly.solo]
    calc
      _ ≤ Poly.toll w (T.menu.marks i j) * h.black (i,j) :=
        mul_le_mul_of_nonneg_left (h.forced x i j U) (Poly.worth h.radii _).le
      _ = (d i)⁻¹ * q (i,j) := by
        change _ = (d i)⁻¹ * (Poly.toll w (T.menu.marks i j) * (d i * h.black (i,j)))
        field_simp [ne_of_gt (hd i)]
  exact (Poly.budgeted h.radii ((hf i).mul_left _) ht).2.trans_eq ((hf i).tsum_mul_left _)

/-- The support-weighted marked price is independent of the field and
test family. The site hit pays the exact scalar K once alongside it. -/
theorem rows (h : RelativeBudget p T w κ (envelopeProduct cost) reg fro) (hc : ∀v, 0 < cost v)
    (hK : P.activities.KBound pK vacuum) (x₀ : X) :
    ∃ m k : ℕ → ℝ, (∀ i, 0 ≤ m i) ∧ (∀ i, 0 ≤ k i) ∧
      SumBudget (fun i => p.mass (P.activities.forced i).support (m i)) (Fintype.card V * (κ * fro)) ∧
      (∀ z : Site n, ∀ s : Finset ℕ, (∑ i ∈ s, if z ∈ (P.activities.forced i).inventory then k i + m i else 0) ≤
        vacuum + Fintype.card V * (κ * fro)) ∧
      ∀ x U i,
        Poly.price (fun v => w v / cost v) ((T.leaf x).contents.each i U - scalarRow P U i) ≤ m i ∧
        Poly.price (fun v => w v / cost v) ((T.leaf x).contents.each i U) ≤ k i + m i ∧
        Poly.price (fun v => w v / cost v) (scalarRow P U i : Poly R) ≤ k i := by
  obtain ⟨m,hm,hmass,ht⟩ := full_rows h.budget x₀
  obtain ⟨k,hk,hHit⟩ := hK
  have hraw : SumBudget m (Fintype.card V * (κ * fro)) := budget_mono hmass hm (fun i => p.loMass _ _ (hm i))
  have hw v : 0 < w v / cost v := div_pos (h.budget.radii v) (hc v)
  have hscalar (U : Config G n) i : Poly.price (fun v => w v / cost v) (scalarRow P U i : Poly R) ≤ k i := by
    change Poly.price _ (Poly.send R.quiet _) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
    exact (hk i).2 U
  refine ⟨m,k,hm,fun i => (hk i).1,hmass,?_,?_⟩
  · intro z s
    apply (le_trans _ (add_le_add (budget_sum (hHit z) s) (budget_sum hraw s)))
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro i _
    by_cases hz : z ∈ (P.activities.forced i).inventory
    · simp only [if_pos hz, if_pos ((P.activities.forced i).inventory_sup hz)]
      exact add_le_add (pK.loMass _ _ (hk i).1) le_rfl
    by_cases hs : z ∈ (P.activities.forced i).support
    · rw [if_neg hz, if_pos hs]
      exact add_nonneg (((hk i).1).trans (pK.loMass _ _ (hk i).1)) (hm i)
    simpa only [if_neg hz, if_neg hs, zero_add] using hm i
  intro x U i
  let E := restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc) (R := R)
  have hE : E (scalarRow P U i : Poly R) = scalarRow P U i := by
    change E (Poly.bead R _) = Poly.bead R _
    have hBead : Poly.bead R (P.activities.K i U : ℂ) = (P.activities.K i U : ℂ) • (1 : Poly R) := by
      simpa only [mul_one] using Poly.product_bead (1 : Poly R) (P.activities.K i U : ℂ)
    rw [hBead,map_smul]
    exact congrArg (fun z : Poly R => (P.activities.K i U : ℂ) • z) (restoreEnvelope_product_one cost hc)
  have hd : Poly.price (fun v => w v / cost v) ((T.leaf x).contents.each i U - scalarRow P U i) ≤ m i := by
    have he : E ((((priceNormalized (envelopeProduct cost) T).leaf x).contents.each i U) - scalarRow P U i) =
        (T.leaf x).contents.each i U - scalarRow P U i := by
      rw [map_sub,hE]
      exact congrArg (fun z : Poly R => z - scalarRow P U i) (restoreEnvelope_each T cost hc x i U)
    rw [← he]
    exact (restoreEnvelope_product_price cost w hc _).trans_le (ht x U i)
  refine ⟨hd,?_,hscalar U i⟩
  have he := Poly.addition hw ((T.leaf x).contents.each i U - scalarRow P U i) (scalarRow P U i)
  rw [sub_add_cancel] at he
  exact (he.trans (add_le_add hd (hscalar U i))).trans_eq (add_comm _ _)

end YM.Integration.SelectedCofactorSupportBudget
end
