import YM.Integration.WilsonPhysicalMarkedDefectRows
import YM.Integration.FVA1Physical.MixedResets.Norm
import YM.MergeProof.Pitch

/-! The signed one-mark field in a physical mixed step. Divide by the actual
positive coarse vacuum after retaining the full marked forced gas. No component
assumption is made about the true flags outside the selected short collar. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open FVA1Physical.MixedResets
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V ι μ X : Type} [Fintype V] [DecidableEq V]
    {Γ : Census V} {A : Passport n V} {P : Rep G n} {w : V → ℝ}
    {κ σ b h g c : ℝ} {E : Tint.Incoming A P X μ Γ} (M : ι → Row A Γ G X)

/-- The full complementary subseries, at the native declared row length; this
is the literal `longMode` integrand of `Round2.CP5ShortMode`. -/
def longRead (p : BudgetPoint) (g : ℝ) (s : Γ.Mode) (x : X) (U : Config G n) : ℂ :=
  ∑' i, if p.B < (M i).length then ((rendered M p g).frame i x U).part s else 0

omit [Fintype V] in
private theorem split_read (p : BudgetPoint) (g : ℝ) (s : Γ.Mode) (x : X) (U : Config G n)
    (paid : Summable (fun i => (rendered M p g).frame i x U)) :
    ((rendered M p g).log x U).part s = shortRead M p g s x U + longRead M p g s x U := by
  let f := fun i => ((rendered M p g).frame i x U).part s
  let S : Set ι := {i | (M i).length ≤ p.B}
  have total : Summable f := (paid.hasSum.map (Poly.get s) (Poly.part_cont s)).summable
  have left : Summable (S.indicator f) := total.indicator _
  have right : Summable (Sᶜ.indicator f) := total.indicator _
  rw [Lamps.log, Poly.share paid, shortRead, longRead]
  change (∑' i, f i) = (∑' i, if (M i).length ≤ p.B then f i else 0) +
    ∑' i, if p.B < (M i).length then f i else 0
  have hl : (fun i => if (M i).length ≤ p.B then f i else 0) = S.indicator f := by
    funext i; by_cases h : (M i).length ≤ p.B <;> simp [Set.indicator, S, h]
  have hr : (fun i => if p.B < (M i).length then f i else 0) = Sᶜ.indicator f := by
    funext i; simp only [Set.indicator, Set.mem_compl_iff, Set.mem_setOf_eq, S, not_le]
  rw [hl, hr, ← left.tsum_add right]
  apply tsum_congr; intro i; by_cases h : i ∈ S <;> simp [h]

/-- The two signed terms in the error against the prescribed short graph: the
original long rows and the complete old ordinary/forced correction. Multiplying by
the actual vacuum gives the physical unnormalized one-mark signal at every field. -/
theorem signed_singleton (receipt : Full P w κ E σ b h) (reserve : 0 ≤ σ)
    (whole : (Tint.Patrol.report M E g).E.Paid w P.p.B P.p.supportExponent c)
    (x : X) (v : V) (U : Config G n) :
    ((Tint.Patrol.report M E g).density x U).part (Γ.fire v) -
      (P.eval U : ℂ)*shortRead M P.p g (Γ.fire v) x U =
      (P.eval U : ℂ)*longRead M P.p g (Γ.fire v) x U +
        ((remainderGallery P E).density x U).part (Γ.fire v) := by
  have data := Full.reads (M := M) (h := receipt) (hr := reserve) (g := g)
    (total := c) whole x U
  obtain ⟨_, _, product, _, _, terms, _⟩ := data
  have hm := Lamps.quiet_of_hasSum x U terms
  have he := (remainderGallery P E).same (receipt.residual_pays reserve)
    P.p.exponent_pos.le receipt.positive x U
  have split := split_read M P.p g (Γ.fire v) x U terms
  change ((rendered M P.p g).log x U).part (Γ.fire v) =
    shortRead M P.p g (Γ.fire v) x U + longRead M P.p g (Γ.fire v) x U at split
  rw [product, MergeProof.Accent.shock Γ, Poly.pass_part _ hm,
    MergeProof.Accent.whisper Γ _ hm v, he, split]
  ring

/-- On the sphere different from zero occupied by this mark, the physical
normalized difference is precisely the real long part plus the original divided
marked correction. The exterior configuration and all forced partners stay free. -/
theorem healthy_singleton (receipt : Full P w κ E σ b h) (reserve : 0 ≤ σ)
    (whole : (Tint.Patrol.report M E g).E.Paid w P.p.B P.p.supportExponent c)
    (x : X) (v : V) (U : Config G n) (positive : 0 < P.eval U)
    (healthy : Healthy P.p.threshold (halo (2*P.p.B+10) {A.origin v}) U) :
    ((Tint.Patrol.report M E g).density x U).part (Γ.fire v) / (P.eval U : ℂ) -
      shortCoefficient M P.p g (Γ.fire v) x U =
      longRead M P.p g (Γ.fire v) x U +
        ((remainderGallery P E).density x U).part (Γ.fire v) / (P.eval U : ℂ) := by
  have eq := signed_singleton M receipt reserve whole x v U
  have hv : v ∈ (Γ.fire v).val := Finset.mem_singleton_self _
  rw [healthy_short M P.p g (Γ.fire v) v hv x U healthy] at eq
  have nonzero : (P.eval U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  field_simp [nonzero]
  linear_combination eq

/-- The same correction is an actual original charged output, including its
complete hard gas, on the very same carrier. The hard bill here is divided
by κ; the undivided support charge in `Full.forced` is h·κ. -/
theorem residual_budget [Nonempty V] [Countable μ] [Nonempty X]
    (receipt : Full P w κ E σ b h) (reserve : 0 ≤ σ)
    (valid : P.activities.ForcedFamily P.p) :
    Nonempty (LocalComparison.FullBudget P.p (Display.taste (remainderGallery P E)) w κ (4*b) h) ∧
      (∀ x U, ((Display.taste (remainderGallery P E)).leaf x).density U =
        (remainderGallery P E).density x U) := by
  obtain ⟨pay, _, _, field⟩ := receipt.viewpoint reserve valid
  exact ⟨pay, fun x U => congrFun (field x) U⟩

end YM.Integration.WilsonPhysicalMarkedDefect

