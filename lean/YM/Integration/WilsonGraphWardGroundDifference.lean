import YangMills.WilsonProof.NativeSupport.WardStressSeries

/-! The three public Ward tests at the first possible disagreement of two series. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Matching.WardStress.GroundDifference
open Function Filter Set MeasureTheory
open scoped BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

def ground (M : MSbar.Coefficients B) (S : Conversion B) {n : ℕ}
    (u w : B.sector 4) (v : Fin n → Label B) (x : Points (n+1)) : ℂ :=
  S.correlation M 0 (Fin.cons ⟨4, u⟩ v) x - S.correlation M 0 (Fin.cons ⟨4, w⟩ v) x

theorem inserted_sub (M : MSbar.Coefficients B) (S : Conversion B)
    (P Q : Series B) (k : ℕ) (earlier : ∀ j < k, P j = Q j)
    {n : ℕ} (a b : Axis) (v : Fin n → Label B) (x : Points (n+1)) :
    inserted M S P k a b v x - inserted M S Q k a b v x =
      ground M S (P k a b) (Q k a b) v x := by
  classical
  have old : (∑ j : Fin k, S.correlation M (k-j.val) (Fin.cons ⟨4, P j.val a b⟩ v) x) =
      ∑ j : Fin k, S.correlation M (k-j.val) (Fin.cons ⟨4, Q j.val a b⟩ v) x :=
    Finset.sum_congr rfl (fun j _ => by rw [earlier j.val j.isLt])
  simp only [inserted, ground, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    Nat.sub_self, old]
  ring

variable {M : MSbar.Coefficients B} {S : Conversion B} {P Q : Series B}

private theorem weighted {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {k : ℕ} (earlier : ∀ j < k, P j = Q j) {n : ℕ}
    (a b : Axis) (v : Fin n → Label B) (w : X → ℂ) (place : X → Points (n+1))
    (hp : Integrable (fun x => w x * inserted M S P k a b v (place x)) μ)
    (hq : Integrable (fun x => w x * inserted M S Q k a b v (place x)) μ) :
    let d := fun x => w x * ground M S (P k a b) (Q k a b) v (place x)
    Integrable d μ ∧ (∫ x, d x ∂μ) =
      (∫ x, w x * inserted M S P k a b v (place x) ∂μ) -
        ∫ x, w x * inserted M S Q k a b v (place x) ∂μ := by
  let f (L : Series B) := fun x => w x * inserted M S L k a b v (place x)
  have eq : (fun x => w x * ground M S (P k a b) (Q k a b) v (place x)) = f P - f Q := by
    funext x
    rw [← inserted_sub M S P Q k earlier]
    exact mul_sub _ _ _
  change Integrable _ μ ∧ _ = _
  rw [eq]
  exact ⟨hp.sub hq, integral_sub hp hq⟩

private theorem sum_zero {ι : Type*} [Fintype ι] (d f q : ι → ℂ)
    (difference : ∀ i, d i = f i - q i) (same : ∑ i, f i = ∑ i, q i) :
    ∑ i, d i = 0 := by
  classical
  calc
    ∑ i, d i = ∑ i, (f i - q i) := Finset.sum_congr rfl (fun i _ => difference i)
    _ = 0 := by rw [Finset.sum_sub_distrib, same, sub_self]

theorem vacuum (p : Determined M S P) (q : Determined M S Q)
    (k : ℕ) (earlier : ∀ j < k, P j = Q j) (a b : Axis)
    (φ : WilsonFamily.SeparatedTest 1) :
    let v := fun i : Fin 0 => (Fin.elim0 i : Label B)
    let d := fun x => φ x * ground M S (P k a b) (Q k a b) v x
    Integrable d ∧ (∫ x, d x) = 0 := by
  have hp := p.vacuum k a b φ
  have hq := q.vacuum k a b φ
  have price := weighted earlier a b (fun i : Fin 0 => Fin.elim0 i)
    (fun x => φ x) id hp.1 hq.1
  exact ⟨price.1, price.2.trans (sub_eq_zero.mpr (hp.2.trans hq.2.symm))⟩

theorem conservation (p : Determined M S P) (q : Determined M S Q)
    {n : ℕ} (k : ℕ) (earlier : ∀ j < k, P j = Q j) (b : Axis)
    (v : Fin n → Label B) (φ : WilsonFamily.SeparatedTest (n+1)) :
    let d := fun a (x : Points (n+1)) => Ward.firstDerivative a (fun y => φ y) x *
      ground M S (P k a b) (Q k a b) v x
    (∀ a, Integrable (d a)) ∧ (∑ a : Axis, ∫ x, d a x) = 0 := by
  have hp := p.conservation k b v φ
  have hq := q.conservation k b v φ
  have price (a : Axis) := weighted earlier a b v
    (Ward.firstDerivative a (fun y => φ y)) id (hp.1 a) (hq.1 a)
  exact ⟨fun a => (price a).1, sum_zero _ _ _ (fun a => (price a).2) (hp.2.trans hq.2.symm)⟩

theorem translation (p : Determined M S P) (q : Determined M S Q)
    {n : ℕ} (k : ℕ) (earlier : ∀ j < k, P j = Q j) (b : Axis)
    (v : Fin (n+1) → Label B) (φ : WilsonFamily.SeparatedTest (n+1))
    (χ : Spacetime → ℝ) (window : ∀ x ∈ tsupport (fun y => φ y), Ward.Window x χ) :
    let d := fun a (z : Spacetime × Points (n+1)) =>
      φ z.2 * ((Maxwell.partialD a χ z.1 : ℝ) : ℂ) *
        ground M S (P k a b) (Q k a b) v (Ward.prepend z.1 z.2)
    (∀ a, Integrable (d a)) ∧ (∑ a : Axis, ∫ z, d a z) = 0 := by
  have hp := p.translation k b v φ χ window
  have hq := q.translation k b v φ χ window
  have price (a : Axis) := weighted earlier a b v
    (fun z : Spacetime × Points (n+1) => φ z.2 * ((Maxwell.partialD a χ z.1 : ℝ) : ℂ))
    (fun z => Ward.prepend z.1 z.2) (hp.2.1 a) (hq.2.1 a)
  exact ⟨fun a => (price a).1,
    sum_zero _ _ _ (fun a => (price a).2) (neg_injective (hp.2.2.trans hq.2.2.symm))⟩

end YangMills.Matching.WardStress.GroundDifference
end

