import YM.Integration.QLocalPhysicalBirthInvoice

/-! Exact maximal site charges put the genuine finite physical source in
the original joint startup menu. One forced coefficient sheet is fixed
before the weights and all physical test evaluations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthMenu
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Ribbon Packets Push.GridApprox.Nil
open scoped Classical BigOperators

variable {n : Side} {ι : Type*} [Fintype ι]

/-- The largest true incidence sum at one site; a finite-stage cost. -/
def sitePrice (X : ι → Support n) (B : ℕ) (u : ι → ℝ) (a : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun x : Site n =>
    ∑ i, if x ∈ X i then u i * Real.exp (a * coverNumber B (X i)) else 0

theorem hit (X : ι → Support n) (B : ℕ) (u : ι → ℝ) (a : ℝ) (hu : ∀ i, 0 ≤ u i) :
    Ac.Hit X B u a (sitePrice X B u a) := by
  intro x
  refine ⟨fun i => ite_nonneg (mul_nonneg (hu i) (Real.exp_nonneg _)) le_rfl,
    Summable.of_finite, ?_⟩
  rw [tsum_fintype]
  exact Finset.le_sup' (fun y : Site n => ∑ i, if y ∈ X i then
    u i * Real.exp (a * coverNumber B (X i)) else 0) (Finset.mem_univ x)

/-- Every other finite-stage site invoice pays this amount. -/
theorem least (X : ι → Support n) (B : ℕ) (u : ι → ℝ) (a : ℝ) {c : ℝ}
    (hc : Ac.Hit X B u a c) : sitePrice X B u a ≤ c := by
  apply Finset.sup'_le
  intro x _
  simpa only [tsum_fintype] using (hc x).2.2

variable {G : Gauge} (R : Run G) (N p L : ℕ) {V : Type} [DecidableEq V] [Fintype V]
  (o : Positions V (R.family.side L p)) (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.rep N p L

/-- The actual two published peak incidences for the positive physical
startup sheet. -/
def price (b : Box (R.family.side L p) → Sheet (Ribbon.Bud V)) (w : V → ℝ) : ℝ :=
  sitePrice (fun i => ActualRunPhysicalPages.cover R p L (d i) o i) (P₀).p.B
      (fun i => (ActualRunPhysicalPages.page R N p L (d i) o i (v i) (B := Ribbon.Bud V)).due w
        (ActualRunPhysicalPages.price R L (d i) (v i))) ((P₀).p.supportExponent-4) +
    sitePrice Prod.fst (P₀).p.B (fun s => wordsPrice w (b s)) ((P₀).p.supportExponent-4)

/-- The same physical sheet and complete mixed corrections give the
native joint menu for all positive independently chosen marker weights. -/
theorem actual (hG : G.Simple) (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L) :
    ∃ b : Box (R.family.side L p) → Sheet (Ribbon.Bud V),
      (∀ s U q, ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ b s q) ∧
      ∀ w : V → ℝ, (∀ i, 0 < w i) →
        MenuSafe (ActualRunFullPages.pages R hG N p L hL o d v) o
          (ActualRunFullPages.prices R p L o d v b) w (price R N p L o d v b w) := by
  obtain ⟨b, hpos, hb⟩ := QLocalPhysicalBirthInvoice.sheet R N p L o d v hL href
  refine ⟨b, hb, fun w hw => ActualRunFullPages.menuSafe R hG N p L hL o d v href b hpos hb w hw ?_ ?_⟩
  · apply hit
    intro i
    exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _))
      (ActualRunPhysicalPages.priced R N p L (d i) hL (href i) (v i) (o.origin i)).2.1
  · apply hit
    intro s
    exact sum_nonneg fun q _ => mul_nonneg (Poly.worth hw q).le (hpos s q)

end YM.Integration.QLocalPhysicalBirthMenu
end
