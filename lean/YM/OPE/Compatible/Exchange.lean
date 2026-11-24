import YM.OPE.Compatible.Transfer

/-!
# Rated ray of a finite signed replacement
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (U:Spec.Final C f S)
variable {I J B l:Type} [FI : Fintype I] [FJ : Fintype J] [Fintype B] {φ : Filter l} {T : l → ℝ} {κ : ℝ}

-- arity I compared with a finite sum of words of arity J, can also take B empty
lemma exchange (O : l → E4) (X : l → I → E4) (Y : B → l → J → E4)
    (p : l → I → S.Tag) (q : B → l → J → S.Tag) (a : B → l → ℂ)
    (hT : Tendsto T φ atTop)
    (hx : Tendsto (fun i => away (X i) (O i)) φ (𝓝 0))
    (hx' : ∀ᶠ i in φ, Injective (X i))
    (hy : ∀ b, Tendsto (fun i => away (Y b i) (O i)) φ (𝓝 0))
    (hy' : ∀ b, ∀ᶠ i in φ, Injective (Y b i))
    (h : ∀ (K:Type) [Fintype K] (w : K → S.Tag) (y : l → K → E4) {δ : ℝ},
      0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → RateLE φ T (fun i =>
        kernel S (beside (X i) (y i)) (beside (p i) w) - ∑ b, a b i *
          kernel S (beside (Y b i) (y i)) (beside (q b i) w)) κ) (k : ℕ) :
    RateLE φ T (fun i => ray U k (X i) (p i) (O i) -
        ∑ b, a b i • ray U k (Y b i) (q b i) (O i)) κ := by
  let N : Unit⊕B → Type := Sum.elim (fun _ => I) (fun _ => J)
  let z : (b : Unit⊕B) → l → N b → E4 := Sum.rec (fun _ => X) Y
  let v : (b : Unit⊕B) → l → N b → S.Tag := Sum.rec (fun _ => p) q
  let c : Unit⊕B → l → ℂ := Sum.elim (fun _ _ => 1) (fun b i => - a b i)
  letI NF : ∀ b, Fintype (N b) := Sum.rec (fun _ => FI)
    (fun _ => FJ)
  have he : Fits N O z φ := by
    constructor
    · rintro (t|t)
      exact hx
      exact hy t
    rintro (t|t)
    exact hx'
    exact hy' t
  have hu : NearProbes N O z v c φ T κ := by
    constructor; intro k hk w y δ hδ hh; apply (h k w y hδ hh).congr
    apply Eventually.of_forall
    intro i; dsimp only; rw [Fintype.sum_sum_type]; conv_rhs => rw [Fintype.sum_unique]
    change _ - _ = 1 * _ + ∑ b:B, (-a b i)* kernel S (beside (Y b i) (y i)) (beside (q b i) w)
    rw [one_mul]; simp_rw [neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]; rfl
  refine (absorb N O z v c hT he hu U.phase.transport.spots U.room.kernel (supplies S) k).congr
    (Eventually.of_forall fun i => ?_)
  dsimp only; rw [Fintype.sum_sum_type,Fintype.sum_unique]
  change ((1:ℂ) • (ray U k (X i) (p i) (O i)) + ∑ b, (-a b i) • ray U k (Y b i) (q b i) (O i)) = _
  simp [sub_eq_add_neg]
end YM.OPE.Cov.Display
