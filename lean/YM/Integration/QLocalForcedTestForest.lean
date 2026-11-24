import YM.Integration.QLocalForcedTestInvoice

/-! Simultaneous marked test and field publication of the original entire
compulsory forest. Its quiet coefficient is the actual gas and its finite
barcode field equals the countable native cluster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalForcedTestForest
open Function Finset Lattice Wilson RG Marker Overlay
open RG3.Script.Picnic LocalComparison LocalComparison.Global MergeProof MergeProof.Accent
open Push.AbsoluteSums QLocalForcedTestInvoice
open scoped BigOperators Classical

private theorem add {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
    {I X : Type*} {w : V → ℝ} {s : I → Support n} {F H : I → X → Poly Γ} {B : ℕ}
    {e a b : ℝ} (hF : Towed w s F B e a) (hH : Towed w s H B e b) :
    Towed w s (fun i z => F i z + H i z) B e (a+b) := by
  obtain ⟨f,hf,hI,hL⟩ := hF
  obtain ⟨g,hg,hJ,hM⟩ := hH
  refine ⟨fun i => f i + g i,hf.add hg,?_,?_⟩
  · intro x
    convert Push.Local.sumBudget_add (hI x) (hJ x) using 1
    funext i
    split_ifs <;> ring
  · intro i
    obtain ⟨v,hv,h1,h2⟩ := hL i
    obtain ⟨w,hw,h3,h4⟩ := hM i
    refine ⟨fun q => v q+w q,fun q => add_nonneg (hv q) (hw q),?_,?_⟩
    · intro z q
      exact (norm_add_le ..).trans (add_le_add (h1 z q) (h3 z q))
    · simpa only [Push.GridApprox.Nil.wordsPrice,mul_add,sum_add_distrib] using add_le_add h2 h4

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
  {X : Type*} {o : V → Site n} {P : Rep G n} (p : BudgetPoint) (T : Taste X o P Γ)
  {w : V → ℝ} {d u κ : ℝ}

private theorem first (i : ℕ) (z : X × Config G n) :
    tally Prod.fst (entry T) i z = ∑' j, entry T (i,j) z := by
  let e : ℕ ≃ {k : ℕ × ℕ // k.1 = i} := {
    toFun j := ⟨(i,j),rfl⟩
    invFun k := k.val.2
    left_inv j := rfl
    right_inv := by rintro ⟨⟨k,j⟩,h⟩; cases h; rfl }
  exact (e.tsum_eq (fun k => entry T k.val z)).symm

private theorem ordinary (hK : P.activities.KBound p κ) :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => Poly.send Γ.quiet (P.activities.K i z.2 : ℂ))
      p.B p.supportExponent κ := by
  obtain ⟨b,hb,hh⟩ := hK
  refine ⟨b,Activities.summable_charge (fun i => (P.activities.forced i).inventory_ne.mono
    (P.activities.forced i).inventory_sup) (fun i => (hb i).1) hh,?_,?_⟩
  · intro x
    convert hh x using 1
    funext i
    unfold BudgetPoint.mass
    split_ifs <;> ring
  · intro i
    simpa only [Poly.quiet_toll,one_mul] using
      (satin (w := w) (fun z : X × Config G n => (P.activities.K i z.2 : ℂ))
        Γ.quiet (b i) (hb i).1 (fun z => by simpa using (hb i).2 z.2))

variable [Fintype V]
variable (B : ForcedBudget p T w d u) (hw : ∀ i, 0 < w i)
  (ho : ∀ i j, (T.menu.marks i j).val.Nonempty) (hK : P.activities.KBound p κ)
include B hw ho hK

theorem rows :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => (T.menu.terms z.1).each i z.2) p.B p.supportExponent
      (κ+(Fintype.card V : ℝ)*(d*u)) := by
  have h := towing (r := fun i : ℕ => (P.activities.forced i).support) Prod.fst (entry T)
    (tagged p T B hw ho) hw
  have he : tally Prod.fst (entry T) = (fun i z => ∑' j,entry T (i,j) z) := funext fun i =>
    funext fun z => first T i z
  rw [he] at h
  exact add (ordinary p (X := X) (Γ := Γ) hK) h

omit B hw ho hK in
def full := tally (MergeProof.barcode P.activities) (fun i (z : X × Config G n) =>
  (T.menu.terms z.1).each i z.2)

theorem spectrum : Towed w Prod.fst (full T) p.B p.supportExponent
    (κ+(Fintype.card V : ℝ)*(d*u)) :=
  towing (MergeProof.barcode P.activities) _ (rows p T B hw ho hK) hw

theorem cluster (x : X) (U : Config G n) :
    (T.menu.terms x).cluster U = field (fun s => full T s (x,U)) (flags P.p.threshold U) :=
  (Accent.rock_out P.activities P.p U (fun i => (T.menu.terms x).each i U) hw
    ((rows p T B hw ho hK).repair hw (x,U)).1).symm

theorem quiet (s : Box n) (z : X × Config G n) :
    (full T s z).part Γ.quiet = QLocalBarcodeDifference.value P.activities s z.2 := by
  have ht := (((tagged p T B hw ho).repair hw z).2)
  have hs (i : ℕ) : Summable (fun j => entry T (i,j) z) := ht.comp_injective
    (i := fun j : ℕ => (i,j)) (fun _ _ h => congrArg Prod.snd h)
  have he (i : ℕ) : ((T.menu.terms z.1).each i z.2).part Γ.quiet = (P.activities.K i z.2 : ℂ) := by
    change (Poly.send Γ.quiet (P.activities.K i z.2 : ℂ) + ∑' j,entry T (i,j) z).part Γ.quiet = _
    rw [Poly.part_plus,Poly.share (hs i)]
    have hz (j : ℕ) : (entry T (i,j) z).part Γ.quiet = 0 := by
      unfold QLocalForcedTestInvoice.entry
      rw [Poly.part_send,if_neg]
      intro hh
      exact (ho i j).ne_empty (congrArg Subtype.val hh.symm)
    simp only [hz,tsum_zero,add_zero,Poly.part_send,ite_true]
  have hf : Summable (fun i : {i : ℕ // MergeProof.barcode P.activities i = s} =>
      (T.menu.terms z.1).each i.val z.2) :=
    ((rows p T B hw ho hK).repair hw z).2.comp_injective Subtype.val_injective
  unfold full tally
  rw [Poly.share hf Γ.quiet]
  exact tsum_congr fun i => he i.val

end YM.Integration.QLocalForcedTestForest
