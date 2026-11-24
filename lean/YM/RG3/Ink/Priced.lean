import YM.RG3.Ink.Combined
import YM.RG3.Letters.Fiscal

/-!
Share-weight portfolio for the full marked-vacuum merger. It buys the
**coefficientwise** envelope, so later publication of separate named
alternatives on these addresses does not pay any factor depending on the
size of the marker space. All hypotheses about pump/cost are numerical:
use small radii and enough forced and support reserves before consuming.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Ink
open Function Set RG Ac Lattice Wilson Marker MeasureTheory Push.Corrected Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {ι μ V : Type*} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}
variable {v : V → Site n} {p : BudgetPoint}

namespace Shelf.Stock
variable {A : Shelf G n ι μ} (X : A.Stock p R v)

def credit (A : Shelf G n ι μ) (g : ι ⊕ μ → Poly R) (c : A.Patch) :=
  ∏ i ∈ A.frame.letters c, g i

variable {g : ι ⊕ μ → Poly R} {B : ℕ} {a χ γ : ℝ} {radii : V → ℝ}

theorem covered (h : ∀ i U, Width.Covered (X.ink i U) (g i)) (c U) :
    Width.Covered (X.cargo c U) (credit A g c) := by
  have hh := Width.bulk (A.frame.letters c) (F:=fun i => X.ink i U) (fun i _ => h i U)
  unfold cargo Letters.Frame.merged
  split
  · exact hh
  exact hh.zero

theorem bought (A : Shelf G n ι μ) (hr : ∀ i,0<radii i)
    (ha : 0 ≤ a) (hχ : 1 ≤ χ) (hγ : 0 ≤ γ)
    (hH : Hit A.frame.read B (A.frame.pump (fun i => Poly.price radii (g i)) χ) (a+1) γ)
    (Green : (B+B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    Hit A.frame.ground B (fun c => Poly.price radii (credit A g c)) a ((Real.exp γ - 1)/χ) := by
  classical
  exact A.frame.pumped B a γ χ _ (fun i => Poly.nonnegative hr _) hχ ha hγ hH Green _
    (fun i => Poly.nonnegative hr _) (fun i => Poly.multiple hr (A.frame.letters i) _)

/-- Absolute summability of input polynomial tray at this fixed torus.
Only qualitative! uses finite-dimensional equivalent norms. -/
theorem tray_absolute (hr : ∀ i,0<radii i) (hg : ∀ i U, Width.Covered (X.hardVal i U) (g (.inl i)))
    (a : ℝ) (ha : 0 ≤ a) (hχ : 1 ≤ χ)
    (hH : Hit A.frame.read B (A.frame.pump (fun i => Poly.price radii (g i)) χ) a γ)
    (U : Config G n) : Summable fun s => ‖X.tray U s‖ := by
  have hk := (YM.RG3.Letters.Frame.from_hit B a γ _ A.frame.nonempty
    (fun i => show 0 ≤ A.frame.pump _ χ i from by
      unfold Letters.Frame.pump
      split
      · exact mul_nonneg (zero_le_one.trans hχ) (Poly.nonnegative hr (g i))
      exact Poly.nonnegative hr (g i)) ha hH)
  let f : ι → ℝ := fun i => χ*Poly.price radii (g (.inl i))
  have he : Summable f := (budget_pull (Sum.inl : ι → ι ⊕ μ) Sum.inl_injective (C:=Fintype.card (Site n)*γ) hk).2.1.congr
    fun _ => if_pos (A.inl_hard _)
  have hf i : 0≤ f i := mul_nonneg (zero_le_one.trans hχ) (Poly.nonnegative hr _)
  obtain ⟨c,hc,H⟩ := Poly.equivalent_norm (R:=R) hr
  exact ((summable_finsetProd_of_summable_nonneg hf he).mul_right c).of_nonneg_of_le
    (fun i => norm_nonneg _) (fun s => by
      apply (H _).trans (mul_le_mul_of_nonneg_right ?_ hc)
      unfold tray
      split
      · exact (Poly.multiple hr ..).trans (Finset.prod_le_prod (fun i _ => Poly.nonnegative hr _)
          (fun i _ => ((hg i U).reprice _ hr).trans (le_mul_of_one_le_left (Poly.nonnegative hr _) hχ)))
      rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _ => hf i)

/-- Address predicate receipts for future flags/integration. Inspected-support
consumer is `UsesFinal.allReads`. We deliberately do *not* count aggregation
at overlapping inspected stencils as a disjoint occurrence when using `stockpile`.
-/
theorem checks (A : Shelf G n ι μ) (p : BudgetPoint)
    (hB : ∀ i, MeasurableSet {U | (A.hard i).extraTest U})
    (hG : ∀ i t U,(A.hard i).extraTest (Lattice.gauge t U) ↔ (A.hard i).extraTest U)
    (hU : ∀ i, UsesFinal p.threshold (A.hard i).support (A.hard i).extraTest)
    (c : A.Patch) :
    MeasurableSet {U | (cargoAddr A p c).extraTest U} ∧
    (∀ t U,(cargoAddr A p c).extraTest (Lattice.gauge t U) ↔ (cargoAddr A p c).extraTest U) ∧
    UsesFinal p.threshold (cargoAddr A p c).support (cargoAddr A p c).extraTest := by
  refine ⟨?_,?_,?_⟩
  · change MeasurableSet {U | ∀ i : ι, Sum.inl i ∈ A.frame.letters c → _}
    have he : {U : Config G n | ∀ i : ι, Sum.inl i ∈ A.frame.letters c → (A.hard i).eligible p.threshold U} =
        ⋂ i : ↥((A.frame.letters c).toLeft),{U | (A.hard i.val).eligible p.threshold U} := by
      ext x; rw [mem_iInter]; constructor
      · exact fun h i => h _ (Finset.mem_toLeft.mp i.property)
      exact fun h i w => h ⟨i,Finset.mem_toLeft.mpr w⟩
    rw [he]
    apply MeasurableSet.iInter; intro i; exact Work.H03.eligible_measurable _ _ (hB i.val)
  · intro t U; exact forall_congr' fun i => imp_congr_right fun _ => Work.H03.eligible_gauge _ _ _ _ (hG i t U)
  intro U W h he; apply propext
  exact forall_congr' fun i => imp_congr_right fun hi => Iff.of_eq
    (Work.H03.reads_larger (A.frame.entries_inside _ hi)
      (Work.H03.eligible_reads _ _ (hU i)) U W h he)

/-- Full marked polynomial attachment at this point, purchased at an
explicit reserve. Across this same transformation a full exponent-plus-
K density consumer will multiply this exact polynomial on either side by the
unmarked path/scalar and appropriately aligned regular log. There is no
conditional normalization inside this operation. -/
theorem fiscally [Fintype μ] (hr : ∀ i,0<radii i) (hg : ∀ i U, Width.Covered (X.ink i U) (g i))
    (ha : 0 ≤ a) (hχ : 1 ≤ χ) (hγ : 0 ≤ γ)
    (hH : Hit A.frame.read B (A.frame.pump (fun i => Poly.price radii (g i)) χ) (a+1) γ)
    (Green : (B+B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    (∀ U, Summable (fun s => ‖X.tray U s‖) ∧ Summable (fun s => ‖X.pack U s‖) ∧
      (∑' b,X.tray U b)*(∏ i : μ, (1+X.slipVal i U))=∑' s,X.pack U s) ∧
    (∀ c U, Width.Covered (X.cargo c U) (credit A g c)) ∧
    (∀ c, Width.LocalCharge p v (cargoAddr A p c).support (X.cargo c)) ∧
    (∀ c U, X.cargo c U ≠ 0 → (cargoAddr A p c).eligible p.threshold U) ∧
    Hit A.frame.ground B (fun c => Poly.price radii (credit A g c)) a ((Real.exp γ - 1)/χ) := by
  refine ⟨fun U => ?_, X.covered hg, X.localCargo, X.cargo_eligible, bought A hr ha hχ hγ hH Green⟩
  have hu := X.tray_absolute hr (fun i U => hg (Sum.inl i) U) (a+1) (by linarith) hχ hH U
  exact ⟨hu,X.stockpile U hu⟩

end Shelf.Stock
end YM.RG3.Ink
