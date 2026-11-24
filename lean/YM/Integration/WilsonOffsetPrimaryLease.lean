import YM.Integration.WilsonOffsetEquationLaw
import YM.Frontier6.Multi.Seams.Shift
import YM.Spec.Closed

/-! The calibrated primary at an arbitrary microscopic position has a
common signed replication price on the enclosing comparison cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetPrimaryLease
open Function Set Filter Lattice Cells Wilson RG Labels Source Push Extraction
open Next.Extract MergeProof PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} {C : Family G}

theorem place {d : ℕ} (N p : ℕ) (v : C.label d) (o : Site (C.side N p)) :
    C.O N p v 0 ∘ Lattice.translate o = C.O N p v o := by
  funext U
  simp only [Family.O,TransferData.cylinder,initial,Function.comp_apply,Pi.smul_apply,
    SectionData.places_trans,zero_add]

theorem purchased (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ k₀ : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≥ k₀, ∀ η : ℝ, 0 < η →
      ∀ᶠ w : ℕ×ℕ in f.fuse, ∃ hn : k ≤ w.1,
        ∀ (x : R.family.label d), ‖x‖ ≤ K → ∀ (j : ℕ) (hj : j ≤ k)
        (o : Site (R.family.side w.1 w.2)) (v : Site (R.family.side j w.2)),
        let T := center R.family.S w.2 (hj.trans hn) (0 : Site (R.family.side w.1 w.2))
        o ∈ T.margin v (3*Cells.span R.family.S hn w.2) →
        ∃ X : Config G (R.family.side w.1 w.2) → ℂ,
          Interior (T.chamber 0) X ∧ T.rootTest (R.family.beta w.1 w.2) X ≤
            A*(R.family.S.a k)^(-(d:ℝ)-δ)+η ∧ T.copy v X = R.family.O w.1 w.2 (b.step d w x) o := by
  obtain ⟨a,ha⟩ := sale.uniform d
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha (0,0))
  let B := 1+a*K
  have pos : 0 < B := by dsimp only [B]; positivity
  obtain ⟨k₀,_,A,hA,hp⟩ := F.room.copies.centered d δ B hδ pos
  refine ⟨k₀,A,hA,?_⟩; intro k hk η hη
  have rich := hp k hk η hη
  change ∀ᶠ w : ℕ×ℕ in f.fuse, ∃ hn : k ≤ w.1, ∀ (v : R.family.label d), ‖v‖ ≤ B →
    ∀ o : Site (R.family.side w.1 w.2), Interior ((center R.family.S w.2 hn o).chamber 0)
    (R.family.O w.1 w.2 v o) ∧ (center R.family.S w.2 hn o).rootTest (R.family.beta w.1 w.2)
    (R.family.O w.1 w.2 v o) ≤ A*(R.family.S.a k)^(-(d:ℝ)-δ)+η at rich
  filter_upwards [rich] with w hw
  obtain ⟨hn,hcash⟩ := hw
  refine ⟨hn,?_⟩; intro x hx j hj o v T inside
  have held : ‖b.step d w x‖ ≤ B := by
    refine ((b.step d w).le_opNorm x).trans ?_
    exact (mul_le_mul (ha w) hx (norm_nonneg _) ha0).trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨fit,upper⟩ := hcash (b.step d w x) held 0
  obtain ⟨X,hX,pX,actual⟩ := Frontier6.Platform.moved_basis F.room.cutoff hn hj v fit upper inside
  exact ⟨X,hX,pX,actual.trans (place ..)⟩

end YM.Integration.WilsonOffsetPrimaryLease
