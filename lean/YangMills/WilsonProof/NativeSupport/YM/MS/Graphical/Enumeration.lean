import YM.MS.Graphical.Enumeration
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Ladder

/-!
# Sector sum

`ambient n` and `insertions h n` enumerate *diagrams*, not budgets for terms
in a solved equation. Multiplicity conventions: work with multisets, use all order
allocations and don't canonicalize left/right in a bulk merge. Doing the
latter without changing the sector weights would give wrong integrals.
`Coverage.lean` proves there are no duplicates (in this grammar) and no missing
valid diagrams of nonzero value on the germ.
-/

set_option autoImplicit false
namespace YM.MS.Graphical.Diagram
open Set Filter Function Finset MeasureTheory
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Lattice Cylinder Motif Literal Halo Outlook Mach
open scoped Topology ContDiff BigOperators



noncomputable section
-- helper `truncate` for wf recursion on arbitrary budget



lemma distribute_ok {S : Finset (ℕ×ℕ)} {L R L' R' : ℕ→Multiset Diagram}
    (hl : ∀ p∈S,L (p.1) = L' p.1) (hr : ∀ p∈S,R (p.2)=R' p.2) :
    distributeS S L R = distributeS S L' R' := by
  unfold distributeS Multiset.bind
  congr 1; apply Multiset.map_congr rfl; intro i hi
  rw [hl _ hi,hr _ hi]

lemma ambient_zero : ambient 0=0 := by unfold ambient; rw [Nat.strongRecOn_eq,if_pos rfl]

lemma truncates {α : Type} [Zero α] (f : ℕ→α) {i k : ℕ} (h : i<k) : truncateD k (fun i _=> f i) i=f i :=
   dif_pos h

lemma ambient_unfold {n : ℕ} (hn : 0<n) :
    ambient n = tower true 4 n ({lit n} + distributeS (shortB n) ambient ambient) := by
  unfold ambient; rw [Nat.strongRecOn_eq];
  rw [if_neg (by omega)]; congr 2; apply distribute_ok
  · exact fun p hp=> truncates _ (Finset.mem_filter.mp hp|>.2.1)
  exact fun p hp=> truncates _ (Finset.mem_filter.mp hp|>.2.2)

lemma mark_unfold (h n : ℕ) :
    insertions h n = tower false h n ({lit n} + distributeS (shortM n) ambient (insertions h)) := by
  unfold insertions; rw [Nat.strongRecOn_eq]; congr 2; apply distribute_ok (fun _ _=>rfl)
  exact fun p hp => truncates _ (Finset.mem_filter.mp hp|>.2)

/- grammar constraints -/
abbrev Is (b : Bool) (n : ℕ) (l : Multiset Diagram) := ∀ k∈l, order k=n ∧ Valid k b
namespace Is
variable {S : Finset (ℕ×ℕ)} {X Y : ℕ → Multiset Diagram} {b : Bool} {l r : Multiset Diagram} {n h : ℕ}
theorem dist (hx : ∀ i∈ S, Is true i.1 (X i.1)) (hy : ∀ i∈ S, Is b i.2 (Y i.2))
    (hp : S ⊆ antidiagonal n) : Is b n (distributeS S X Y) := by
  intro k hk; obtain ⟨i, hi, he⟩ := Multiset.mem_bind.mp hk
  obtain ⟨x,hw,hu⟩:= Multiset.mem_bind.mp he
  obtain ⟨y,hv,rfl⟩:= Multiset.mem_map.mp hu
  obtain ⟨hX,hS⟩:= hx i hi _ hw; obtain ⟨hY,hT⟩:= hy i hi _ hv
  exact ⟨ by rw [order,hX,hY]; exact Finset.mem_antidiagonal.mp (hp hi),hS,hT⟩
theorem sum (he : Is b n l) (hx : Is b n r) : Is b n (l+r) := fun x hx' =>
  (Multiset.mem_add.mp hx').elim (he x) (hx x)
theorem towers (he : Is b n l) : Is b n (tower b h n l) := by
  intro k hk; obtain ⟨x,hx,H⟩:= Multiset.mem_bind.mp hk
  obtain ⟨h1,h2⟩:= he x hx; obtain ⟨hw,hU⟩:= ladder_order x h2 _ k H; exact ⟨hw.trans h1, hU⟩
theorem litV (hp : b = true → 0<n) : Is b n {lit n} := by simp only [Is,Multiset.mem_singleton]; exact fun k hk=> hk.symm ▸ ⟨rfl,hp⟩
end Is

theorem is_ambient (n : ℕ) : Is true n (ambient n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
     rcases eq_or_ne n 0 with h|h;
     · subst n; simp [Is,ambient_zero]
     have ht : 0<n := Nat.pos_of_ne_zero h
     rw [ambient_unfold ht]; exact Is.towers (Is.sum (Is.litV (fun _=>ht))
       (Is.dist (fun i hi=> ih i.1 (Finset.mem_filter.mp hi|>.2.1))
         (fun i hi=> ih i.2 (Finset.mem_filter.mp hi|>.2.2)) (Finset.filter_subset ..)))

theorem is_insertions (h n : ℕ) : Is false n (insertions h n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
     rw [mark_unfold]
     exact Is.towers (Is.sum (Is.litV (by intro h; contradiction)) (Is.dist
       (fun i _ => is_ambient i.1) (fun i hi => ih i.2 (Finset.mem_filter.mp hi|>.2))
       (Finset.filter_subset ..)))

end
end YM.MS.Graphical.Diagram
