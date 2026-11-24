import YM.Integration.SignedLowOutputAsymptotic

/-! The actual normalized Wilson source at every intermediate level for
independent, physically selected, possibly moving grades and fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedPhysicalWords
open Filter Set Function Spec OPE OPE.Orbits Pert.Position SignedTreeTransport Trace.Pilot
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} {n : ℕ}

def sample (v : Fin n → S.Tag) (x : Points n) (b : ℕ × ℕ) (j : ℕ) (hj : j ≤ b.1) : ℂ :=
  mean C b.1 b.2 j hj (WilsonWholeLimit.product (d := fun l => (v l).1) x.ofLp (fun l => (v l).2) b.1 b.2)

theorem fixed (F : Final C f S) (hS : Services C f S) (v : Fin n → S.Tag)
    (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ b.1),
      ‖sample v x b j hj-S.useAt S x v‖ ≤ ε := by
  let w := Orbits.names (d := fun l => (v l).1) (fun l => (v l).2)
  filter_upwards [SignedCompactWilson.rounded_read F hS w K hK hsep hε] with b hb x hx j hj
  rw [sample,mean_eq F.room.cutoff _ _ _ _ _ (WilsonWholeLimit.product_continuous ..),←dist_eq_norm]
  exact (hb x hx).le

theorem dilated (F : Final C f S) (hS : Services C f S) (r : ℝ) (hr : 0 < r)
    (v : Fin n → S.Tag) (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ b : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ b.1),
      ‖sample v (r • x) b j hj - S.useAt S (r • x) v‖ ≤ ε := by
  have hs : (fun x : Points n => r • x) '' K ⊆ conf n := by
    rintro _ ⟨x,hx,rfl⟩
    exact Work.A05.smul_conf hr (hsep hx)
  filter_upwards [fixed F hS v _ (hK.image (continuous_id.const_smul r)) hs hε] with b hb x hx j hj
  exact hb _ ⟨x,hx,rfl⟩ j hj

theorem moving (F : Final C f S) (hS : Services C f S) (v : ℝ → Fin n → S.Tag)
    (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n) (δ : ℝ → ℝ)
    (he : ∀ᶠ r in trail, 0 < δ r) :
    ∀ᶠ r in trail, ∀ᶠ b : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ b.1),
      ‖sample (v r) (r • x) b j hj - S.useAt S (r • x) (v r)‖ ≤ δ r := by
  filter_upwards [he,self_mem_nhdsWithin] with r ht hr
  exact dilated F hS r hr (v r) K hK hsep ht

end YM.Integration.SignedPhysicalWords
