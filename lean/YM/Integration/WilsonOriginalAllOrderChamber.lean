import YM.Integration.WilsonOriginalAllOrderPublicFields
import YM.OPE.Cards.Literal

/-! Fixed-chamber physical copy estimates for the actual microscopic fields
selected on the public hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAllOrderChamber
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open MeasureTheory Set Cells Wilson Extraction Word Push Next.Phase Push.RelayDifference OPE.Cards
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius

/-- Both chamber arrays may have arbitrarily many occupied cells (and zero
cells). Each occurrence uses its literal field and its own paid price. -/
def Licensed {G : Gauge} (S : Schedule) (N p m : ℕ) (β : ℝ) {ι : Type*}
    (X : ι → Config G (S.side N p) → ℂ) (A : ι → ℝ) : Prop :=
  ∀ (n n' : ℕ) (a : Fin n → ι) (b : Fin n' → ι) (W₀ W : Tiling (S.side N p)),
    W₀.kind = .link → W.kind = .link → W₀.base = W.base → W₀.side.val ∣ W.side.val →
    ∀ hm : m ≤ N, Cells.span S hm p ∣ W₀.side.val → Cells.span S hm p ∣ W.side.val →
    ∀ (u : Fin n → Site (S.side N p)) (v : Fin n' → Site (S.side N p)),
      (∀ i, Inside W₀ (3 * Cells.span S hm p) (u i)) →
      (∀ i j, i≠j → W₀.side.val < separation (u i) (u j)) →
      (∀ i, Inside W (3 * Cells.span S hm p) (v i)) →
      (∀ i j, i≠j → W.side.val < separation (v i) (v j)) →
      (∀ i j, W.side.val < separation (v i) (u j)) → Seam G (S.side N p) β →
      ‖moment β (fun U => (∏ i, (X (b i) ∘ translate (v i)) U) *
        ∏ j, (X (a j) ∘ translate (u j)) U)‖ ≤ (∏ i, A (b i)) * ∏ j, A (a j)

theorem at_cutoff {G : Gauge} {S : Schedule} {N p m : ℕ} {β : ℝ} {ι : Type*}
    {X : ι → Config G (S.side N p) → ℂ} {A : ι → ℝ}
    (card : ∀ i, PaidAt S N p m β (A i) (X i)) : Licensed S N p m β X A := by
  intro n n' a b W₀ W h₀ hW base divide hm small large u v first apart second apart' across seam
  exact Cards.plant h₀ hW base divide hm small hm large u (X ∘ a) (A ∘ a) v (X ∘ b) (A ∘ b)
    first apart second apart' across (fun i => card (a i)) (fun i => card (b i)) seam

variable {G : Gauge} {R : Run G}

/-- Elect the representatives only once per finite basis and radius. Their
copy estimate already includes all licensed copy counts at each receiving
cutoff. The proof uses the original Wilson moment and torus geometry. -/
theorem original {v : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family v S} {l : Ultrafilter (ℕ × ℕ)} {r A : ℝ} {j m D : ℕ}
    (pool : Pool F l r j m D A) {ι : Type*} [Finite ι] (d : ι → ℕ) (fit : ∀ i, d i ≤ D)
    (field : (i : ι) → S.Field (d i)) :
    ∃ (Z : (i : ι) → R.family.label (d i)) (Y : (i : ι) → ℕ × ℕ → R.family.label (d i)),
      (∀ i, S.project (d i) (Z i) = field i ∧ Tendsto (Y i) (l : Filter (ℕ × ℕ)) (𝓝 (Z i))) ∧
      ∀ᶠ u : ℕ × ℕ in (l : Filter (ℕ × ℕ)),
        (∀ i, Next.UVStress.quota R.family (d i) j u.1 u.2 (Y i u) ≤
          R.family.S.a j^(d i)*A*cost F (d i) r (field i)) ∧
        Licensed R.family.S u.1 u.2 m (R.family.beta u.1 u.2)
          (fun i => R.family.O u.1 u.2 (Y i u) 0) (fun i => A*cost F (d i) r (field i)) := by
  obtain ⟨Z,Y,limits,price⟩ := WilsonOriginalAllOrderPublicFields.cylinders pool d fit field
  refine ⟨Z,Y,limits,?_⟩
  filter_upwards [price] with u bill
  exact ⟨fun i => (bill i).1,at_cutoff (fun i => (bill i).2)⟩

end YM.Integration.WilsonOriginalAllOrderChamber
end
