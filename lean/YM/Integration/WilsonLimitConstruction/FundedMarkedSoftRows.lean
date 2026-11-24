import YM.Integration.WilsonLimitConstruction.FundedCoverMarkedCorrection
import YM.Integration.PositiveWilsonMarkedInput
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Add the genuinely masked nonempty marked rows before the true forced
cluster product. Old ordinary and compulsory addresses have literal injections. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedMarkedSoftRows
open Function Lattice Wilson RG Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {n : Side} {P : Rep G n} {o : V→Site n}

structure Rows (X : Type) (Γ : Census V) (G : Gauge) (n : Side) where
  mode : ℕ → Γ.Mode
  site : ℕ → Support n
  value : X → ℕ → Config G n → ℂ

variable (L : Rows X Γ G n)

def wave (p : BudgetPoint) (x : X) (U : Config G n) (i : ℕ) : Poly Γ :=
  Poly.send (L.mode i) (masked p.threshold (L.site i) (L.value x i) U)

def negative : Rows X Γ G n := { L with value := fun x i U => -(L.value x i U) }

theorem negative_wave {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    (L : Rows X Γ G n) (p : BudgetPoint) (x : X) (U : Config G n) (i : ℕ) :
    wave (negative L) p x U i = -wave L p x U i := by
  classical
  unfold wave negative
  by_cases h : Healthy p.threshold (L.site i) U
  · simp only [masked_eq _ _ _ _ h]
    ext v
    by_cases hv : v=L.mode i <;> simp [Poly.part_neg,Poly.part_send,hv]
  · simp only [masked_ne _ _ _ _ h,Poly.send_zero,neg_zero]

def append (T : Taste X o P Γ) : Taste X o P Γ where
  menu := { T.menu with
    rays := fun k => Sum.elim T.menu.rays L.mode (Equiv.natSumNatEquivNat.symm k)
    branch := fun k => Sum.elim T.menu.branch L.site (Equiv.natSumNatEquivNat.symm k)
    regular := fun x k =>
      Sum.elim (T.menu.regular x) (L.value x) (Equiv.natSumNatEquivNat.symm k) }
  root := T.root
  tag := T.tag
  site := T.site
  score := T.score

variable (T : Taste X o P Γ)

theorem old_row {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {P : Rep G n} {o : V→Site n} (L : Rows X Γ G n) (T : Taste X o P Γ) (i : ℕ) (x : X) :
    (append L T).menu.regular x (Equiv.natSumNatEquivNat (.inl i))=T.menu.regular x i ∧
    (append L T).menu.branch (Equiv.natSumNatEquivNat (.inl i))=T.menu.branch i := by
  simp [append]

theorem new_row {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {P : Rep G n} {o : V→Site n} (L : Rows X Γ G n) (T : Taste X o P Γ) (i : ℕ) (x : X) :
    (append L T).menu.regular x (Equiv.natSumNatEquivNat (.inr i))=L.value x i ∧
    (append L T).menu.branch (Equiv.natSumNatEquivNat (.inr i))=L.site i := by
  simp [append]

theorem forced {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {P : Rep G n} {o : V→Site n} (L : Rows X Γ G n) (T : Taste X o P Γ) :
    (append L T).menu.force=T.menu.force ∧ (append L T).menu.marks=T.menu.marks := ⟨rfl,rfl⟩

theorem cluster {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {P : Rep G n} {o : V→Site n} (L : Rows X Γ G n) (T : Taste X o P Γ) (x : X) (U : Config G n) :
    ((append L T).leaf x).contents.cluster U=(T.leaf x).contents.cluster U := rfl

theorem bands_active {G : Gauge} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {P : Rep G n} {o : V→Site n} (L : Rows X Γ G n) (T : Taste X o P Γ) (x : X) (old : (T.menu.terms x).Active)
    (proper : ∀i,(L.mode i).val.Nonempty)
    (pins : ∀ i j, j∈(L.mode i).val → T.menu.origins j∈L.site i)
    (regular : ∀i,P.p.Regular (L.site i) (L.value x i)) : ((append L T).menu.terms x).Active := by
  refine ⟨?_,?_,?_,old.occurs,old.retained,old.inspects,
    old.keeps,old.meas,old.invi⟩
  · intro i
    obtain ⟨j,rfl⟩ := Equiv.natSumNatEquivNat.surjective i
    cases j with
    | inl k => simpa [append,Taste.leaf,View.terms] using old.proper k
    | inr k => simpa [append,Taste.leaf,View.terms] using proper k
  · intro i j
    obtain ⟨k,rfl⟩ := Equiv.natSumNatEquivNat.surjective i
    cases k with
    | inl k => simpa [append,Taste.leaf,View.terms] using old.pins k j
    | inr k => simpa [append,Taste.leaf,View.terms] using pins k j
  · intro i
    obtain ⟨j,rfl⟩ := Equiv.natSumNatEquivNat.surjective i
    cases j with
    | inl k => simpa [append,Taste.leaf,View.terms] using old.regular k
    | inr k => simpa [append,Taste.leaf,View.terms] using regular k

theorem active (x : X) (old : (T.leaf x).Active)
    (proper : ∀i,(L.mode i).val.Nonempty)
    (pins : ∀ i j, j∈(L.mode i).val → T.menu.origins j∈L.site i)
    (regular : ∀i,P.p.Regular (L.site i) (L.value x i)) : ((append L T).leaf x).Active :=
  ⟨bands_active L T x old.articles proper pins regular,old.captions⟩

theorem log (x : X) (U : Config G n) {s : Poly Γ}
    (old : Summable (fun i => (T.leaf x).contents.ray i U))
    (rows : HasSum (wave L P.p x U) s) :
    ((append L T).leaf x).log U=(T.leaf x).log U+s := by
  let f := fun i => ((append L T).leaf x).contents.ray i U
  have union : HasSum (f ∘ Equiv.natSumNatEquivNat)
      ((∑' i : ℕ,(T.leaf x).contents.ray i U)+s) := by
    apply HasSum.sum
    · simpa [f,Function.comp_def,append,Taste.leaf,View.terms,Bands.ray] using old.hasSum
    · simpa [f,Function.comp_def,append,Taste.leaf,View.terms,Bands.ray,wave] using (show HasSum (fun i=>wave L P.p x U i) s from rows)
  have h := (Equiv.natSumNatEquivNat.hasSum_iff).1 union
  change ((∑ v : V, Poly.send (Γ.fire v) (T.menu.global x v))+∑' i, f i)+_ =
    ((∑ v : V, Poly.send (Γ.fire v) (T.menu.global x v))+∑' i,(T.leaf x).contents.ray i U)+_+s
  rw [h.tsum_eq]
  abel

theorem density (x : X) (U : Config G n) {s : Poly Γ}
    (old : Summable (fun i => (T.leaf x).contents.ray i U))
    (rows : HasSum (wave L P.p x U) s) (act : (T.leaf x).Active) (quiet : s.part Γ.quiet=0) :
    ((append L T).leaf x).density U=Poly.pass s*(T.leaf x).density U := by
  rw [Deck.density,Deck.density,log L T x U old rows,cluster,
    Next.Rank.Exponential.pass_add _ _ (PositiveWilsonMarkedInput.quiet_log _ act U) quiet,
    mul_smul_comm]
  congr 1
  ring

end YM.Integration.WilsonLimitConstruction.FundedMarkedSoftRows
end
