import YM.QuadraticLocal.Germ.Affinity
import YM.QuadraticLocal.Kiosk
/-!
# Static qlocal address retention and canonized mask-query attachments in polynomial algebra

Transpose root/test-stencil-footprints within given geometry, including old flagged dependencies.
Operates all modes simultaneously, at arbitrary given function test budget data K A.
Geometry X_v chosen beforehand by caller; if addresses are chargeable only on some locations,
you may distinguish further the slot name before building an input packet. Don't minimize X from
observed zeros. Layout retains these complete sets even when any of the tests zero out, at all
unpromoted predicate alternatives charged by old mask rules.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace YM.QuadraticLocal.Affinity
open Function Filter Finset MeasureTheory RemainderComparison
open Marker Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat
variable {θ:Type} [DecidableEq θ] {α:Type*} {n:Side}{G:Gauge}{q:ℝ}
variable {R:Census θ} (X:θ→Support n){o:θ→Site n}
variable {Y:θ→Type*}[∀ i,AddCommGroup (Y i)] {𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ][∀ i,Module 𝕜 (Y i)]
variable (A:∀ i,Set (Y i))(K:∀ i,Submodule 𝕜 (Y i)) {p:BudgetPoint} {F : Ovens.Code G n}{P:ℕ→ForcedAddress G n}{I:Type*}
structure Addressable (T:Support n)(s:Finset θ)(f:Wallet A→ℂ):Prop where
   advice : Attn K A s f
   announces t (h:f t≠0)(i:θ): i∈s→ X i⊆T
-- Hard declarations: declare on X footprint containment; for any missing piece carries IDENTICAL ZERO at all U t. This doesn't assume every K slot can fit a passive junk theta origin. Look at RetainsDeclared in Integration. Compact lemmas.
structure Stencil (T:Support n) (f:Wallet A→Poly R):Prop where
    each (i:R.Mode) : Addressable X A K T i.val fun t=> (f t).part i
namespace Addressable
variable {X A K}{S T : Support n}{s q:Finset θ}{f g:Wallet A→ℂ}
lemma gone : Addressable X A K T s fun _=>0:= ⟨Attn.silent,fun _ h=> (h rfl).elim⟩
lemma steady (v:ℂ): Addressable X A K T ∅ fun _=>v := ⟨Attn.solid v,fun _ _ i hi=> (Finset.notMem_empty _ hi).elim⟩
lemma widen (h:Addressable X A K S s f)(hp:S⊆T): Addressable X A K T s f:=⟨h.advice,fun i hi v hv=> (h.announces i hi v hv).trans hp⟩
lemma plus (h:Addressable X A K S s f)(hh:Addressable X A K S s g): Addressable X A K S s (fun t=>f t+g t):= by
    refine ⟨h.advice.plus hh.advice, fun t ht i hi=> ?_⟩
    by_contra hn; apply ht; rw [not_not.mp (fun hx=>hn (h.announces _ hx _ hi)),not_not.mp (fun hx=> hn (hh.announces _ hx _ hi)),add_zero] -- synthesis?
lemma bind (h:Addressable X A K S s f)(hh:Addressable X A K S q g)(hp:Disjoint s q): Addressable X A K S (s∪q) (fun t=>f t*g t):=by
    refine ⟨h.advice.bind hh.advice hp, fun t ht v hv=>?_⟩
    rcases mem_union.mp hv with hv|hv; exact h.announces _ (left_ne_zero_of_mul ht) _ hv; exact hh.announces _ (right_ne_zero_of_mul ht) _ hv
lemma total {ι:Type*}(p: Finset ι)(g:ι→Wallet A→ℂ) (hf:∀i∈p,Addressable X A K S s (g i)): Addressable X A K S s (fun t=> ∑ j∈p,g j t):=by
    induction p using Finset.induction with
    | empty=> simp_rw [sum_empty]; exact gone
    | insert j s hj ih=>simp_rw [sum_insert hj]; exact (hf j (mem_insert_self _ _)).plus (ih fun i hi=> hf i (mem_insert_of_mem hi))
lemma gather {ι:Type*}(g:ι→Wallet A→ℂ)(hf: ∀ i,Addressable X A K S s (g i)) (hg:∀ t,Summable (fun i=>g i t)): Addressable X A K S s (fun t=>∑' i,g i t):=by
    refine ⟨Attn.gather _ (fun i=>(hf i).advice) hg, fun t ht v hv=> ?_⟩
    contrapose! ht; exact (tsum_congr (g:=fun _=>0) (fun j=> not_not.mp (fun hz=>ht ((hf j).announces t hz v hv)))).trans tsum_zero -- pushes not subset ?
end Addressable
namespace Stencil
variable {X A K} {S T : Support n} {f g : Wallet A→Poly R}
lemma zero : Stencil X A K S fun t=>(0:Poly R):=⟨fun i=> by simp_rw [Poly.part_nil]; exact Addressable.gone⟩
lemma widen (h:Stencil X A K S f)(ht:S⊆T):Stencil X A K T f:= ⟨fun i=>(h.each i).widen ht⟩
lemma const (c:Poly R)(h:∀ i,i≠R.quiet→c.part i=0): Stencil X A K T fun _=> c:=by
    refine ⟨fun i=>?_⟩; by_cases he:i=R.quiet; subst i; exact Addressable.steady _; simp_rw [h i he]; exact Addressable.gone
lemma one:Stencil X A K T fun _ =>(1:Poly R) := const 1 fun i hi=> by simp [Poly.one_part,hi]
lemma mul (hf:Stencil X A K T f)(hg:Stencil X A K T g): Stencil X A K T (fun t=> f t*g t):=by
    refine ⟨fun i=>?_⟩; simp_rw [Poly.part_mul]; apply Addressable.total; intro j _; apply Addressable.total; intro k _; split
    next h=> exact h.2 ▸ (hf.each j).bind (hg.each k) h.1
    next=> exact Addressable.gone
lemma sum (h:Stencil X A K S f)(hg:Stencil X A K S g): Stencil X A K S (fun t=>f t+g t):=⟨fun i=>by simp_rw [Poly.part_plus]; exact (h.each i).plus (hg.each i)⟩ -- Lean naming bad
lemma prod {ι:Type*}(p:Finset ι)(g:ι→Wallet A→Poly R) (h:∀ i∈p,Stencil X A K S (g i)):Stencil X A K S (fun t=>∏ j∈p,g j t):=by
    induction p using Finset.induction with
    | empty=> simp_rw [prod_empty]; exact one
    | insert i s hi ih=> simp_rw [prod_insert hi]; exact (h i (mem_insert_self _ _)).mul (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma gather {ι:Type*}(g:ι→Wallet A→ Poly R)(h:∀ i,Stencil X A K S (g i))(hp:∀ t,Summable (fun i=>g i t)): Stencil X A K S (fun t=>∑' i,g i t):= ⟨fun i=> by
    simp_rw [Poly.share (hp _)]; exact Addressable.gather _ (fun j=>(h j).each i) fun t=> ((hp t).hasSum.mapL (Poly.get i)).summable⟩
end Stencil
open Ovens Ovens.Pipes Progress.DirectedRecipe Payments Push Push.AbsoluteSums RG3 Lattice Wilson
open Fusion Fusion.Attached Kiosk Canopy
structure Crown (H:Hard (Wallet A) p P F o R) :Prop where
   lesson i U : Stencil X A K (P i).support fun t=> H.hard t i U
structure Taut (L:Lamps (Wallet A) I G p o R):Prop where
   house (i:I)(v:θ): v∈ (L.mode i).val → X v⊆ L.ground i
   adv i U : Attn K A (L.mode i).val fun t=> L.nominal t i U
structure Collared (P:Rep G n)(L:Gallery (Wallet A) I o P R) :Prop where
   lamps : Taut X A K L.E
   hard : Crown X A K L.K
namespace Crown
variable {X A K}
lemma shape {P Q:ℕ→ ForcedAddress G n}{F W: Code G n} {L:Hard (Wallet A) p P F o R} (hP:P=Q)(hQ:F=W)(hl:Crown X A K L): Crown X A K (Kiosk.shape hP hQ L):=by subst Q W; exact hl
variable {B C: Activities G n}
variable (H:Hard (Wallet A) p B.forced B.K o R)
lemma rename {f g:ℕ↪ℕ} (h:Readdress p f g B C)(hV:Crown X A K H): Crown X A K (H.readdress h):=by
    refine ⟨fun i U=>?_⟩
    by_cases he:i∈ Set.range g
    · obtain ⟨j,rfl⟩:=he; unfold Hard.readdress; dsimp only; simp_rw [stuffed, h.sup]; exact hV.lesson _ _
    unfold Hard.readdress; dsimp only; simp_rw [blank _ _ he]; exact Stencil.zero
open RG3.Ink
variable (P:Pipes G n)
lemma stock (e:ℕ≃P.Pellet) (D:Wallet A→ (layout P).Stock p R o)
    (h:∀ i U,Stencil X A K (P.patch i) (fun t=> (D t).ink i U)) (i:ℕ)(U:Config G n): Stencil X A K (addr e p i).support (fun t=>marked e (D t) i U):=by
    simp_rw [marked_eq]; split; next ht=> exact Stencil.prod _ _ (fun j hj=> (h j U).widen (show P.patch j ⊆ (addr e p i).support from Finset.subset_biUnion_of_mem _ hj))
    next=> exact Stencil.zero
variable {f w a M:ℝ}
private lemma candles {P:Pipes G n}{d:Tap G n}(h:Hard.Soft P d p)(L:Hard (Wallet A) p P.kernel d.forced o R)(i:ℕ)(U:Config G n): Stencil X A K (P.softer i) (fun t=>(L.stock h t).slipVal i U) := Stencil.const (Poly.send R.quiet ↑(reach d (.inr i) U)) (fun _ hi=> (Poly.part_send ..).trans (if_neg hi))
lemma passage (D:Kiosk.First p B C f w a) (h:Crown X A K H): Crown X A K (D.led H) :=
    Crown.shape _ _ ⟨fun i U=> Crown.stock _ D.roll ((Kiosk.shape D.oldP D.oldV H).stock D.softens) (fun j U=>by
      cases j; exact (Crown.shape D.oldP D.oldV h).lesson _ _; exact candles D.softens _ _ _) i U⟩
open Rack
variable [Countable I]
lemma usage {P:Pipes G n}{d:Tap G n}(h:Hard.Soft P d p)(L:Hard (Wallet A) p P.kernel d.forced o R)(M:ShiftRows (Wallet A) I G p o R)(he:Crown X A K L)(hp: ∀ i U,Stencil X A K (M.place i).val (fun t=> M.soap t i U)) : Crown X A K (M.poster h L):=by
    let P':= drawer G n; let L':=L.readdress (A:=P.pours d) (Rack.preserves P d p); have he' := Crown.rename _ (A:=A) (B:=P.pours d) (C:=(drawer G n).pours (Rack.widen P d)) (Rack.preserves P d p) he -- fix
    refine ⟨fun i U=> Crown.stock P' (folio G n) (M.stock h L) (fun j U=>?_) i U⟩
    rcases j with i|i; exact he'.lesson _ _
    refine Stencil.sum (candles (X:=X) (A:=A) (K:=K) (Canopy.ShiftRows.softWide h) L' i U) ?_
    change Stencil _ _ _ ((drawer G n).softer i) (fun t=>M.placed t i U);
    unfold ShiftRows.placed; by_cases he:i∈ Set.range M.packPost
    · obtain ⟨j,rfl⟩:=he; rw [M.packSite]; simp_rw [stuffed]; exact hp j U
    simp_rw [blank _ _ he]; exact Stencil.zero
lemma second (D:Kiosk.Second p B C f w a M)(M:ShiftRows (Wallet A) I G p o R)(h:Crown X A K H)(hp:∀ i U, Stencil X A K (M.place i).val (fun t=> M.soap t i U)) : Crown X A K (Kiosk.Second.canopy H M D):= Crown.shape _ _ (Crown.usage _ _ _ (Crown.shape D.oldP D.oldV h) hp)
end Crown
end YM.QuadraticLocal.Affinity
