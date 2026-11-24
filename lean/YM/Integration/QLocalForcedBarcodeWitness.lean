import YM.Integration.QLocalForcedTestForest
import YM.Push.GRID_APPROXIMATION.Hit
import YM.Integration.LocalComparisonFunctionalRetains

/-! A nonquiet coefficient of the original signed grouped bank comes from
a genuine nonzero original tagged row in its own compulsory inventory.
The joint support places every marker and every dirty inventory site at
the distance paid by the same connected cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalForcedBarcodeWitness
open Function Finset Lattice Wilson RG Marker Overlay
open RG3.Script.Picnic LocalComparison LocalComparison.Global
open MergeProof MergeProof.Accent Push.AbsoluteSums Push.GridApprox.Attach
open QLocalForcedTestInvoice QLocalForcedTestForest
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
  {Γ : Census V} {o : V → Site n} {X : Type*} {P : Rep G n} (p : BudgetPoint)
  (T : Taste X o P Γ) {w : V → ℝ} {d u κ : ℝ} (B : ForcedBudget p T w d u)
  (hw : ∀ i, 0 < w i) (ho : ∀ i j, (T.menu.marks i j).val.Nonempty) (hK : P.activities.KBound p κ)
include B hw ho hK

omit hK in
theorem at_index (i : ℕ) (z : X × Config G n) (q : Γ.Mode) (hne : q ≠ Γ.quiet)
    (h : ((T.menu.terms z.1).each i z.2).part q ≠ 0) :
    ∃ j, T.menu.marks i j = q ∧ T.menu.force z.1 i j z.2 ≠ 0 := by
  by_contra hn
  apply h
  have ht := ((tagged p T B hw ho).repair hw z).2
  have hs : Summable (fun j => QLocalForcedTestInvoice.entry T (i,j) z) := ht.comp_injective
    (i := fun j : ℕ => (i,j)) (fun _ _ hh => congrArg Prod.snd hh)
  change (Poly.send Γ.quiet (P.activities.K i z.2 : ℂ) + ∑' j,QLocalForcedTestInvoice.entry T (i,j) z).part q = _
  rw [Poly.part_plus,Poly.share hs]
  have hj (j : ℕ) : (QLocalForcedTestInvoice.entry T (i,j) z).part q = 0 := by
    unfold QLocalForcedTestInvoice.entry
    rw [Poly.part_send]
    split
    · rename_i hq
      by_contra hz
      exact hn ⟨j,hq.symm,hz⟩
    · rfl
  simp only [hj,tsum_zero,Poly.part_send,if_neg hne,add_zero]

theorem atom (s : Box n) (z : X × Config G n) (q : Γ.Mode) (hne : q ≠ Γ.quiet)
    (h : (full T s z).part q ≠ 0) :
    ∃ i j, MergeProof.barcode P.activities i = s ∧ T.menu.marks i j = q ∧
      T.menu.force z.1 i j z.2 ≠ 0 := by
  by_contra hn
  apply h
  have he (i : ℕ) (hi : MergeProof.barcode P.activities i = s) :
      ((T.menu.terms z.1).each i z.2).part q = 0 := by
    by_contra nz
    obtain ⟨j,hmark,hrow⟩ := at_index p T B hw ho i z q hne nz
    exact hn ⟨i,j,hi,hmark,hrow⟩
  have hf : Summable (fun i : {i : ℕ // MergeProof.barcode P.activities i = s} =>
      (T.menu.terms z.1).each i.val z.2) :=
    ((rows p T B hw ho hK).repair hw z).2.comp_injective Subtype.val_injective
  unfold full tally
  rw [Poly.share hf q]
  calc _ = ∑' _i : {i : ℕ // MergeProof.barcode P.activities i = s}, (0 : ℂ) :=
        tsum_congr fun i => he i.val i.property
    _ = 0 := tsum_zero

omit B hw ho hK in
structure Rooted (address : V → Support n) (s : Box n) (q : Γ.Mode) (flags : Support n) : Prop where
  addresses v : v ∈ q.val → address v ⊆ s.1
  charged : s.2.Nonempty
  inside : s.2 ⊆ s.1
  flags_eq : s.1 ∩ flags = s.2

theorem rooted {address : V → Support n} (hret : FunctionalRetains T address)
    (ha : ∀ x, (T.leaf x).Active) (s : Box n) (z : X × Config G n) (q : Γ.Mode)
    (hne : q ≠ Γ.quiet) (h : (full T s z).part q ≠ 0) : Rooted address s q (flags P.p.threshold z.2) := by
  obtain ⟨i,j,hi,hq,hrow⟩ := atom p T B hw ho hK s z q hne h
  subst s
  subst q
  exact ⟨fun v hv => hret.forced i j v ⟨z.1,z.2,hrow⟩ hv,
    (P.activities.forced i).inventory_ne,(P.activities.forced i).inventory_sup,
    ((ha z.1).articles.keeps i j z.2 hrow).1⟩

omit B hw ho hK [Fintype V] in
theorem Rooted.near {address : V → Support n} {s : Box n} {q : Γ.Mode} {hot : Support n}
    (h : Rooted address s q hot) (k : ℕ) {y : Site n} (hy : y ∈ s.2) :
    y ∈ hot ∧ ∀ v ∈ q.val, ∀ x ∈ address v, separation x y < (coverNumber k s.1 + 1)*leg k := by
  have hhot : y ∈ s.1 ∩ hot := h.flags_eq.symm ▸ hy
  refine ⟨(mem_inter.mp hhot).2,?_⟩
  intro v hv x hx
  exact (Nat.div_lt_iff_lt_mul (leg_pos k)).mp
    (Nat.lt_succ_of_le (distance_charge s.1 k x y (h.addresses v hv hx) (h.inside hy)))

end YM.Integration.QLocalForcedBarcodeWitness
