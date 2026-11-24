import YM.RG3.Held.Fresh

/-!
# Tracking separate test slots through the WHOLE polynomial (for real
or complex multilinear presentations, at a fixed threshold). Insertion
arguments/held address tests never repeated in products. Thus once analytic
prescription/corrected test inputs have authorized multilinearity and common
operator norms, no output held order is spent for joining on flags. For a
merely unit-Θ bound one can extend summability with `Letter.cost` first;
explicitly require full sum receipts whenever taking `Letter.assembly`. A
common budget with `Inspector` is one sufficient input on all tested Θ;
otherwise require actual statement outside unit Θ if asserting the global
presentation. Differentiations in U itself only inside regular laws! No
mixed∂/tsum exchange.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Held
open Function Finset Marker RG Ink Press RG3.Forms Overlay MeasureTheory Ac Push.Corrected Lattice Wilson Extra.Trajectories
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type*} [DecidableEq V] {R : Census V}
variable (K : Type*) [RCLike K] [Algebra K ℂ] [ContinuousConstSMul K ℂ]
variable (T : V → Type*) [∀ i,NormedAddCommGroup (T i)] [∀ i,NormedSpace K (T i)]
variable (A : View (Π v, T v) V G n P R)

namespace View
structure Author : Prop where
  regular i U : Letter K T (A.rays i).val (fun z => A.regular z i U)
  force i j U : Letter K T (A.marks i j).val (fun z => A.force z i j U)
  unit i : Letter K T {i} fun z => A.global z i

namespace Author
variable {K T A}
omit [ContinuousConstSMul K ℂ] in
lemma send (i : R.Mode) (f : (Π v, T v) → ℂ) (h : Letter K T i.val f) : Published (K:=K) T fun z => Poly.send i (f z) := by
  intro j; by_cases he : j=i
  · subst j
    simp only [Poly.part_send,↓reduceIte]; exact h
  simp only [Poly.part_send,if_neg he]; exact Letter.still

lemma hard (h : A.Author K T) (hs : ∀ x i U,Summable (fun j => (A.terms x).tagged i j U)) i U :
    Published (K:=K) T fun x => (A.terms x).each i U := by
  apply Published.sum (Published.const _ (fun j hj => ?_)) (Published.assembly _ ?_ (fun x => hs x i U))
  · intro j; exact send (A.marks i j) (fun x => A.force x i j U) (h.force i j U)
  exact (Poly.part_send R.quiet _ _).trans (if_neg hj)

omit [ContinuousConstSMul K ℂ] in
lemma woven (h : A.Author K T) i U : Published (K:=K) T fun x => (A.terms x).ray i U := by
  apply send (A.rays i) _ ?_
  change Letter _ _ _ (fun x => masked _ (A.branch i) (A.regular x i) U)
  by_cases hx : Healthy P.p.threshold (A.branch i) U
  · simp only [masked_eq _ _ _ _ hx]; exact h.regular i U
  simp only [masked_ne _ _ _ _ hx]; exact Letter.still
end Author
end View

-- propagate past stock into the marked entries. Uses no on-field estimators
-- on the merged products; just full polynomial product.
namespace ShelfStock
variable {K T} {ι μ : Type*} [Countable ι] [Countable μ] {W : Shelf G n ι μ}
variable {v : V → Site n} {p : BudgetPoint} {f : (Π v, T v) → W.Stock p R v}

omit [ContinuousConstSMul K ℂ] [Countable ι] [Countable μ] in
theorem reclosed (h : ∀ i U,Published (K:=K) T fun x => (f x).hardVal i U)
    (hh : ∀ i U,Published (K:=K) T fun x => (f x).slipVal i U) (i U) :
    Published (K:=K) T fun x => (stamp (f x)).flow i U := by
  classical
  unfold Press.stamp Shelf.Stock.cargo Letters.Frame.merged; dsimp only; split
  · apply Published.prod; rintro (a|a) _
    · exact h _ _
    exact hh _ _
  exact Published.zero
end ShelfStock

namespace View
variable {K T}
variable {α : Type*} [Countable α] {v : V → Site n} (d : (Π v, T v) → Article α P.p G R v) (slot : α → ℕ) [Nonempty V]

omit [ContinuousConstSMul K ℂ] in
theorem fits (h : A.Author K T) (he : ∀ i U, Published (K:=K) T fun x => (d x).flow i U) : (A.impression d slot).Author K T where
  regular := h.regular
  unit := h.unit
  force i j U := by
    classical
    by_cases hi : j ∈ Set.range (pin (α:=Article.Key α R))
    · obtain ⟨c,rfl⟩ := hi
      change Letter K T ((((A.impression d slot).terms (0:(Π v, T v))).marks i (pin c)).val) (fun x => ((A.impression d slot).terms x).entries i (pin c) U)
      simp_rw [View.enrolled, Article.marked_pin, Article.scored_pin]
      unfold Article.scored; split
      · exact he ..
      exact Letter.still
    change Letter K T _ (fun x => ((A.impression d slot).terms x).entries i j U)
    simp_rw [View.enrolled,Article.scored_blank _ _ _ _ _ hi]; exact Letter.still
end View

section Family
variable {J : Type*}
-- allows Feed from unrestricted inputs. Include `real pure` constant as a separate
-- scalar uniformly (otherwise K-dependent scalar identity over (Π v, T v) needs further
-- classification). Requires summability for all z in the claimed external-test
-- equality, not just on a provided ball.
structure Binding (f : (Π v, T v) → Feed G n R J) where
  dictionary : J → Column R n
  pinned x : dictionary = (f x).column
  auth i U : Letter K T (dictionary i).2.val fun x => (f x).value i U
  prices x : ∃ w B a u δ, (∀ i,0<w i) ∧ 0≤a ∧ (f x).Worth w B a u δ

namespace Binding
variable {K T} {f : (Π v, T v) → Feed G n R J}
lemma typed (h : Binding K T f) (i U) : Published (K:=K) T fun x => (f x).slip i U := by
  let s := {l:J // h.dictionary l=i}
  let F : (Π v, T v)→ℂ := fun x => ∑' c : s,(f x).value c.val U
  have he (x:(Π v, T v)) : s=(f x).office i := by unfold Feed.office; rw [← h.pinned x]
  have hs (x) : F x=(f x).row i U := by
    unfold F s; rw [h.pinned x]; rfl
  have hu (x) : Summable fun c : s => (f x).value c.val U := by
    obtain ⟨w,B,a,u,δ,hw,ha,HP⟩ := h.prices x
    exact (HP.usage ha hw U).of_norm.comp_injective Subtype.val_injective
  have hd : Letter K T i.2.val F := Letter.assembly _ (fun c => by
    simpa only [c.property] using h.auth (c:s).val U) hu
  unfold Feed.slip
  split
  · apply View.Author.send; simp_rw [← hs]; exact hd
  next hn =>
    simp_rw [← hs]
    have hi : ∀ x, F x=F 0 := fun x => hd.stay x 0 (by rw [(show i.2=R.quiet from not_ne_iff.mp hn)]; exact fun i hh => (notMem_empty i hh).elim) -- domain c ≡ c.2
    simp_rw [hi]
    exact Published.const _ (fun j hj => by unfold Poly.bead; exact (Poly.part_send _ _ _).trans (if_neg hj))
end Binding

variable [Nonempty V] [Fintype V] [Countable J] {K T}
variable {d : (Π v, T v) → Deck R P} {f : (Π v, T v) → Feed G n R J} {w s k E} {v : V → Site n} (Q : Inspector d f w s k E v)

theorem restores (h : Accessible P) (B : View (Π v, T v) V G n P R) (hB : B.Author K T) (HB : A.Author K T)
    (hf : ∀ x,B.terms x=(d x).contents) (H : Binding K T f) :
    (Q.stay A h).Author K T := by
  letI : Countable (catalog (P:=P) (R:=R)).Patch := by unfold Shelf.Patch Letters.Frame.Patch; infer_instance
  apply A.fits Q.stampPage (wharf (p:=P.p) P h) HB
  intro i U
  -- f x Stock has variable origins, `ShelfStock.reclosed` parameter v fixed but need change; simpler direct Published.prod
  unfold Inspector.stampPage Press.stamp; change Published T (K:=K) (fun x => (Q.planner x).stock.cargo i U)
  unfold Shelf.Stock.cargo Letters.Frame.merged; split
  · apply Published.prod
    rintro (l|l) _
    · change Published (K:=K) T fun x => (d x).contents.each l U
      have hx : ∀ x i U, Summable (fun j => (d x).contents.tagged i j U) := fun x i V => ((Q.planner x).toBillboard.qual (Q.planner x).radii
        (by linarith [P.p.exponent_pos]) i V).stock
      simp_rw [← hf] at hx ⊢
      exact hB.hard hx _ _
    exact H.typed l U
  exact Published.zero
end Family
end YM.RG3.Held
