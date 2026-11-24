import YM.RG3.Ink.Priced

/-!
# qlocal — exact, common-vacuum fusion on the construction's reclosure route

Both mergers in the all-order path (`Marlin` and `finish`) use `Ovens.Pipes.fused`.
Extend this very merger to a full polynomial in the markers. Retain the
**same Pellet**, including all the old hard addresses (not just the union-of-supports or a
merged patch inferred from the marked density). In particular the quiet projection is on exactly
the selected, unperturbed vacuum. Allow both hard and soft to carry polynomial factors, including
test-dependent *signed* ones. Use with `θ` a test packet, with the majors chosen before `θ`.
Selections with conflicting marks multiply in `Marker.Poly`, never taking an absolute value in the
formula used for evaluation. The hit estimate, with one hard reserve *per merged component*, uses
no bound involving the total number of marks (use at provisional radii for rough arrays) or the
period/volume. Coefficient envelopes are prior to summation over labels and the test choices.
`Width.LocalCharge` certifies origin coverage for every nonzero coefficient.

This fills the countable-slip AND particular-vacuum-link needs (contrast the very useful
`Forms.Test.produce/stay` routes). Uses `Shelf.Stock` merge math from RG3; extends its bill /
exact identity from finite soft alphabets. Analytic supplier conditions, especially paying such
strong hit rates already before merger, are not inferred from equivalence; see later applications.

By `soft` here we mean mask-change factors (e.g. from re-expressing the additive regular model),
already zero when their support is healthy. This file doesn't itself estimate any jet.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace YM.QuadraticLocal.Fusion
open Function Filter Finset Lattice Wilson RG Ac Marker
open Push.Corrected Push.AbsoluteSums MeasureTheory RG3 RG3.Ink Ovens Ovens.Pipes
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type*} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ : Type*}

private def split : Finset ι × Finset μ ≃ Finset (ι ⊕ μ) := (@Finset.sumEquiv ι μ).toEquiv.symm
local instance instITS : IsTopologicalSemiring (Poly R) where

section Stock
variable {A : Shelf G n ι μ} (S : A.Stock p R o)
variable {f : ι ⊕ μ → Poly R} {B : ℕ} {w : V → ℝ} {a χ γ : ℝ}
lemma stockpileInfinite
    (hw : ∀ i, 0 < w i) (ha : 0 ≤ a) (hχ : 1 ≤ χ)
    (hC : ∀ i U, Width.Covered (S.ink i U) (f i))
    (hH : Hit A.frame.read B
      (A.frame.pump (fun i => Poly.price w (f i)) χ) a γ) (U : Config G n) :
    Summable (S.tray U) ∧ Summable (fun z : Finset μ => ∏ i ∈ z, S.slipVal i U) ∧
      HasSum (S.pack U) ((∑' b, S.tray U b) * ∏' i : μ, (1 + S.slipVal i U)) := by
  let f' i := Poly.price w (f i)
  have hn i : f' i ≤ A.frame.pump f' χ i := by
    unfold Letters.Frame.pump; split
    · exact le_mul_of_one_le_left (Poly.nonnegative hw _) hχ
    exact le_rfl
  let g i := S.ink i U
  have h i : 0 ≤ Poly.price w (g i) := Poly.nonnegative hw _
  have he i : Poly.price w (g i) ≤ A.frame.pump f' χ i := ((hC i U).reprice _ hw).trans (hn i)
  have hs : Summable fun i => Poly.price w (g i) :=
    (Letters.Frame.from_hit B a γ _ A.frame.nonempty
      (fun i => (h i).trans (he i)) ha hH).2.1.of_nonneg_of_le h he
  let sH := S.tray U
  let sS (z : Finset μ) := ∏ i∈z, S.slipVal i U
  let L s := Poly.price w (sH s); let K s := Poly.price w (sS s)
  have hi_s : Summable K :=
    (summable_finsetProd_of_summable_nonneg (fun i => h (.inr i))
        (hs.comp_injective Sum.inr_injective)).of_nonneg_of_le (fun _ => Poly.nonnegative hw _)
        (fun z => Poly.multiple hw z _)
  have hi_h : Summable L :=
    (summable_finsetProd_of_summable_nonneg (fun i => h (.inl i))
        (hs.comp_injective Sum.inl_injective)).of_nonneg_of_le (fun _ => Poly.nonnegative hw _)
        (fun z => by
          unfold L sH Shelf.Stock.tray; split
          · exact Poly.multiple hw z _
          rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _ => h (.inl i))
  have hprod : Summable fun i : Finset ι × Finset μ => sH i.1 * sS i.2 := (Poly.budgeted hw
    (budget_prod (f:=L) (W:=K) ⟨fun _ => Poly.nonnegative hw _, hi_h, le_refl _⟩
      ⟨fun _ => Poly.nonnegative hw _, hi_s, le_refl _⟩).2.1 (fun i => Poly.multiplication hw ..)).1
  let D := A.frame
  let F (s : Finset (ι ⊕ μ)) := D.before (flags p.threshold U) g s
  have heq (z : Finset ι × Finset μ) : F (split z) = sH z.1 * sS z.2 := S.disjSum_tray ..
  have hh := (Poly.budgeted hw hi_h fun i => le_refl (L i)).1
  have hk := (Poly.budgeted hw hi_s fun i => le_refl (K i)).1
  have hp : Summable F := split.summable_iff.mp (hprod.congr fun i => (heq i).symm)
  have hl : ∀ i, ¬D.Hard i → g i ≠ 0 → ¬Disjoint (D.read i) (flags p.threshold U) := by
    rintro (i|i) ht
    · exact (ht (A.inl_hard i)).elim
    exact S.flagged i U
  obtain ⟨hq,hR⟩ := D.reindex _ g hl (fun x => x) rfl
  refine ⟨hh, hk, ?_⟩
  have he : (∑' i, S.pack U i) = (∑' b, S.tray U b) * ∏' i : μ, (1 + S.slipVal i U) := calc
    _ = ∑' b, F b := hR.symm
    _ = ∑' z : Finset ι × Finset μ, F (split z) := (split.tsum_eq ..).symm
    _ = _ := by simp_rw [heq, tprod_one_add hk]; exact (hh.tsum_mul_tsum hk hprod).symm
  exact he ▸ (show Summable (S.pack U) from hq.mp hp).hasSum
end Stock

/- convert the supported alphabet. -/
def layout (X : Pipes G n) : Shelf G n ℕ ℕ := ⟨X.kernel,X.softer,X.sites⟩
lemma patch_iff (s : Finset Ovens.Label) : X.contains s ↔
    Spark (layout X).frame.read s ∧ (∃ i∈s,(layout X).frame.Hard i) ∧
      (layout X).frame.OldOK s := by
  constructor
  · rintro ⟨⟨i,hi⟩,h,hc⟩
    refine ⟨h, ⟨.inl i, mem_toLeft.mp hi,(layout X).inl_hard i⟩, ?_⟩
    rintro (i|i) hi (j|j) hj hne hh hh'
    · exact hc (mem_toLeft.mpr hi) (mem_toLeft.mpr hj) (Sum.inl_injective.ne_iff.mp hne)
    · exact ((layout X).inr_hard j hh').elim
    · exact ((layout X).inr_hard i hh).elim
    exact ((layout X).inr_hard i hh).elim
  rintro ⟨h,hh,hc⟩
  refine ⟨?_, h, ?_⟩
  · obtain ⟨i|i,hi,h⟩ := hh
    · exact ⟨i,mem_toLeft.mpr hi⟩
    exact ((layout X).inr_hard i h).elim
  exact fun i hi j hj hn => hc (mem_toLeft.mp hi) (mem_toLeft.mp hj) (Sum.inl_injective.ne hn)
    ((layout X).inl_hard _) ((layout X).inl_hard _)

def patchEquiv (X : Pipes G n) : X.Pellet ≃ (layout X).Patch where
  toFun c := ⟨c.val, (patch_iff _).mp c.property⟩
  invFun c := ⟨c.val, (patch_iff _).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
lemma inventory_eq (s : Finset Ovens.Label) : (layout X).frame.inventory s = X.plot s := by
  ext x; constructor
  · intro hx; obtain ⟨i|i,h,hx⟩ := mem_biUnion.mp hx
    · exact mem_biUnion.mpr ⟨i,mem_toLeft.mpr h,hx⟩
    exact False.elim (notMem_empty x hx)
  intro h; obtain ⟨i,h,hx⟩ := mem_biUnion.mp h; exact mem_biUnion.mpr ⟨Sum.inl i,mem_toLeft.mp h,hx⟩
variable (e : ℕ ≃ X.Pellet)
def toPatch : ℕ ≃ (layout X).Patch := e.trans (patchEquiv X)
lemma support_eq (i) : (layout X).frame.ground (toPatch e i) = (addr e p i).support := rfl
lemma owns_eq (i) : (layout X).frame.owns (toPatch e i) = (addr e p i).inventory := inventory_eq _
lemma addr_eq (i) : Shelf.Stock.cargoAddr (layout X) p (toPatch e i) = Ovens.Pipes.addr e p i := by
  have h : (fun U => ∀ j, Sum.inl j ∈ (layout X).frame.letters (toPatch e i) → ((layout X).hard j).eligible p.threshold U) = condition e p i := by
    funext U; exact propext (forall_congr' fun j => imp_congr (mem_toLeft.symm) Iff.rfl)
  unfold Shelf.Stock.cargoAddr addr

  congr 1; exact owns_eq (p:=p) e i

namespace Attached
variable (S : (layout X).Stock p R o)

def marked (i : ℕ) (U : Config G n) : Poly R := S.cargo (toPatch e i) U

lemma markedLocal (i : ℕ) : Width.LocalCharge p o (addr e p i).support (marked e S i) :=
  addr_eq e i ▸ S.localCargo (toPatch e i)
lemma markedEligible (i : ℕ) (U) (h : marked e S i U ≠ 0) : (addr e p i).eligible p.threshold U :=
  addr_eq e i ▸ S.cargo_eligible (toPatch e i) U h
lemma marked_eq (i : ℕ) (U : Config G n) : marked e S i U = if (addr e p i).eligible p.threshold U
    then ∏ j∈ (e i).val, S.ink j U else 0 := by
  by_cases h : (addr e p i).eligible p.threshold U
  · rw [if_pos h]; unfold marked Shelf.Stock.cargo Letters.Frame.merged
    rw [if_pos (show _ from (owns_eq (p:=p) e i).symm ▸ h.1)]; rfl
  exact (not_ne_iff.mp fun hn => h (markedEligible e S i U hn)).trans (if_neg h).symm

-- Need quiet parts on **ALL** tests and fields, incl on labels with no non-quiet partner.
structure WithQuiet (d : Tap G n) : Prop where
  hard j U : (S.hardVal j U).part R.quiet = d.forced j U
  soft j U : (S.slipVal j U).part R.quiet = ((Real.exp (d.logarithm j U)-1 : ℝ) : ℂ)
lemma WithQuiet.ink {S : (layout X).Stock p R o} (h : WithQuiet S d) (i : Ovens.Label) (U) :
    (S.ink i U).part R.quiet = ↑(Ovens.Pipes.reach d i U) := by
  cases i; exact h.hard _ _; exact h.soft _ _
lemma WithQuiet.marked {S : (layout X).Stock p R o} (h : WithQuiet S d) (i : ℕ) (U) :
    (marked e S i U).part R.quiet = ((solid e p d i U : ℝ) : ℂ) := by
  suffices he : ∀ s : Finset Ovens.Label, (∏ j∈ s,S.ink j U).part R.quiet = ((∏ j∈ s,Ovens.Pipes.reach d j U : ℝ) : ℂ) by
    rw [Attached.marked_eq, solid]; split; exact he _; exact (Poly.part_nil _).trans (by simp)
  intro s; induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty,Poly.one_part,if_true,Complex.ofReal_one]
  | insert i s hi ih => rw [prod_insert hi,prod_insert hi,Poly.quiet_mul,h.ink,ih]; simp
end Attached

namespace Attached
open Shelf.Stock
-- expose receipts and the transition, so existing same Rep can be the output's unmarked dictionary.
def packet (A : Activities G n) (p : BudgetPoint) (K : ℕ → Config G n → Poly R)
    (U : Config G n) (l : Finset ℕ) := if A.admissible p U l then ∏ i ∈ l,K i U else 0

variable (d) (S : (layout X).Stock p R o)
lemma tray_eq (U : Config G n) : S.tray U = packet (X.pours d) p S.hardVal U := by
  funext i; unfold tray packet Activities.admissible; split; rw [if_pos (show _ from ‹_›)]; rw [if_neg (show _ from ‹_›)]
lemma pack_eq (U : Config G n) :
    S.pack U ∘ (toPatch e).finsetCongr = packet (fused e p d) p (marked e S) U := by
  funext b
  let g := toPatch e
  change S.pack U (b.map g.toEmbedding) = _
  let f := addr e p
  have hinv i : (layout X).frame.owns (g i) = (f i).inventory := owns_eq e _
  have ht : (fused e p d).admissible p U b ↔ (layout X).frame.ValidNew (flags p.threshold U) (b.map g.toEmbedding) := by
    unfold Activities.admissible Letters.Frame.ValidNew; refine and_congr ?_ ?_
    · constructor
      · intro he i hi j hj hne; obtain ⟨i,hpi,rfl⟩ := mem_map.mp hi; obtain ⟨j,hpj,rfl⟩ := mem_map.mp hj; exact he hpi hpj (g.injective.ne_iff.mp hne)
      intro he i hi j hj hne; exact he (mem_map_of_mem _ hi) (mem_map_of_mem _ hj) (g.injective.ne hne)
    apply iff_of_eq; congr 1; rw [Finset.map_eq_image]; ext x; simp only [Finset.mem_biUnion,mem_image, Equiv.toEmbedding_apply, exists_exists_and_eq_and]; simp_rw [hinv]; rfl
  unfold pack Letters.Frame.after packet; rw [← ht]; split; swap; · rfl
  exact Finset.prod_map b _ _

abbrev wallet (f : Ovens.Label → Poly R) (i : ℕ) : Poly R := credit (layout X) f (toPatch e i)

variable {f : Ovens.Label → Poly R} {w : V → ℝ} {a χ γ : ℝ}
omit d S in
lemma payment
    (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (hχ : 1 ≤ χ) (hγ : 0 ≤ γ)
    (hH : Hit X.patch p.B (fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i)) (a+1) γ)
    (hG : (p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    Hit (fun i => (addr e p i).support) p.B (fun i => Poly.price w (wallet e f i)) a ((Real.exp γ - 1)/χ) := by
  apply fun k => budget_pull (toPatch e) (toPatch e).injective (bought (layout X) hw ha hχ hγ ?_ hG k)
  unfold Letters.Frame.pump
  have he : (fun i : Ovens.Label => if (layout X).frame.Hard i then χ*Poly.price w (f i) else Poly.price w (f i)) =
      fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i) := by
    funext i; cases i <;> simp only [Shelf.inl_hard,Shelf.inr_hard, ↓reduceIte, Sum.elim_inl,Sum.elim_inr,one_mul]
  rw [he]; exact hH

omit e d in
private lemma pumpHit
    (hH : Hit X.patch p.B (fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i)) a γ) :
    Hit (layout X).frame.read p.B ((layout X).frame.pump (fun i => Poly.price w (f i)) χ) a γ := by
  unfold Letters.Frame.pump
  have he : (fun i : Ovens.Label => if (layout X).frame.Hard i then χ*Poly.price w (f i) else Poly.price w (f i)) =
      fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i) := by
    funext i; cases i <;> simp only [Shelf.inl_hard,Shelf.inr_hard, ↓reduceIte, Sum.elim_inl,Sum.elim_inr,one_mul]
  rw [he]; exact hH

lemma total
    (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (hχ : 1 ≤ χ)
    (hH : Hit X.patch p.B (fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i)) a γ)
    (hC : ∀ i U, Width.Covered (S.ink i U) (f i)) (U : Config G n) :
    Summable (packet (X.pours d) p S.hardVal U) ∧
    Summable (fun z : Finset ℕ => ∏ i ∈ z, S.slipVal i U) ∧
    HasSum (packet (fused e p d) p (marked e S) U)
      ((∑' b, packet (X.pours d) p S.hardVal U b) * ∏' i, (1 + S.slipVal i U)) := by
  rw [← tray_eq, ← pack_eq (X:=X)]
  obtain ⟨h₁,h₂,h₃⟩ := stockpileInfinite S hw ha hχ hC (pumpHit hH) U
  exact ⟨h₁,h₂,(toPatch e).finsetCongr.hasSum_iff.mpr h₃⟩
end Attached

section Apply
open Attached
variable {T : Type*} (S : T → (layout X).Stock p R o)
variable {f : Ovens.Label → Poly R} {w : V → ℝ} {a χ γ : ℝ}

/-- Publication for the chosen unmarked merger. Test-dependent hard and slip factors!
The coefficient majorant for the *same* Pellet works jointly on all tests and fields and is
chosen explicitly; its hit price pays with one hard reserve at the lowered exponent. All supports,
including hard internal extra predicates, stay fixed. Quantitative price is on forced terms not
partition-function estimates. Use as well with charged radii (slots retain previous gains via those
radii through re-expression). This is the transport step itself; includes the one-marker, mixed,
zero-marker/vacuum and general-count cases. -/
theorem merger
    (hQ : ∀ t, Attached.WithQuiet (S t) d)
    (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (hχ : 1 ≤ χ) (hγ : 0 ≤ γ)
    (hC : ∀ i U t, Width.Covered ((S t).ink i U) (f i))
    (hH : Hit X.patch p.B (fun i => Sum.elim (fun _ => χ) (fun _ => 1) i * Poly.price w (f i)) (a+1) γ)
    (hG : (p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    Hit (fun i => (addr e p i).support) p.B (fun i => Poly.price w (wallet e f i)) a ((Real.exp γ - 1)/χ) ∧
    (∀ i t, Width.LocalCharge p o (addr e p i).support (marked e (S t) i) ∧
      ∀ U, (marked e (S t) i U≠0 → (addr e p i).eligible p.threshold U) ∧
        Width.Covered (marked e (S t) i U) (wallet e f i) ∧
        (marked e (S t) i U).part R.quiet = (solid e p d i U :ℂ)) ∧
    ∀ t U,
      Summable (packet (X.pours d) p (S t).hardVal U) ∧
      Summable (fun z : Finset ℕ => ∏ i ∈ z, (S t).slipVal i U) ∧
      HasSum (packet (fused e p d) p (marked e (S t)) U)
        ((∑' b, packet (X.pours d) p (S t).hardVal U b) * ∏' i, (1 + (S t).slipVal i U)) :=
  ⟨payment e hw ha hχ hγ hH hG, fun i t =>
    ⟨markedLocal e _ _, fun U => ⟨markedEligible e _ _ _,
      (S t).covered (fun i U => hC i U t) _ U, WithQuiet.marked e (hQ t) i U⟩⟩,
    fun t U => total d e (S t) hw (add_nonneg ha zero_le_one) hχ hH (fun i U => hC i U t) U⟩
end Apply
end YM.QuadraticLocal.Fusion
