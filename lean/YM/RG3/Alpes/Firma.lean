import YM.RG3.Alpes.Chord
import YM.RG3.Script.Picnic.Stamina
/-! # Authorizing costs even after pressure merger (all typed variants on
 SAME q.P. Allows no stroke correction on Φ doses unless those poses stamped
 here with ALL addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Alpes
open Function Filter Lattice RG Wilson Marker Finset RG3.Held RG3.Forms RG3.Ink RG3.Press RG3.Script RG3.Script.Picnic Overlay
open scoped Topology ContDiff Matrix.Norms.Frobenius Classical BigOperators
variable {V : Type*}{T:V→Type*}[∀ i,NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)]
  {n:Side}[DecidableEq V]{R:Census V}{A:Support n}{G:Gauge}{P:Rep G n}
namespace Vine
variable (X:Vine n T)
def Verse (A:Support n)(f:Dais T→Poly R):Prop:=∀ i,X.Rune i.val A fun z=>(f z).part i
namespace Verse
variable {f g:Dais T→Poly R}
lemma still : X.Verse A (0:Dais T→Poly R):=fun _=> Rune.still _
lemma same (p:Poly R)(h:∀i,i≠R.quiet→p.part i=0): X.Verse A fun _=>p:=by
    intro i; by_cases he:i=R.quiet
    · subst i; exact Rune.const _ _
    simp_rw [h i he]; exact Rune.still _
lemma send {i:R.Mode}{t:Dais T→ℂ}(h:X.Rune i.val A t): X.Verse A fun z=>Poly.send i (t z):=by
    intro j; simp only [Poly.part_send]; by_cases he:j=i
    · subst i; simp only [ite_true]; exact h
    simp_rw [if_neg he]; exact Rune.still _
variable {X}
lemma soar {B:Support n}(h:X.Verse A f)(he:A⊆B):X.Verse B f:=fun i=>(h i).soar he
lemma sum (h:X.Verse A f)(he:X.Verse A g): X.Verse A (f+g):=fun i=> (h i).remit (he i)
lemma product (h:X.Verse A f)(he:X.Verse A g) : X.Verse A (f*g):=by
  intro i; change X.Rune _ _ (fun v=> (f v*g v).part i)
  simp only [Poly.part_mul]; refine Rune.total _ _ fun j _=> Rune.total _ _ fun k _=>?_
  by_cases hp:Poly.merges j k i
  · simp only [if_pos hp]; exact hp.2 ▸ (h j).bind (he k) hp.1
  simp only [if_neg hp]; exact Rune.still _
lemma prod {ι}(q:Finset ι)(Y:ι→Dais T→Poly R)(h:∀ i∈q,X.Verse A (Y i)): X.Verse A fun z=>∏ i∈q,Y i z:=by
    induction q using Finset.induction_on with
    | empty=>simp; exact same _ 1 fun i h=>by simp [h]
    | insert i s hi ih=>simp only [prod_insert hi]; exact (h i (mem_insert_self ..)).product (ih fun _ he=> h _ (mem_insert_of_mem he))
lemma assembly {ι}(f:ι→Dais T→Poly R)(h:∀ i,X.Verse A (f i))(he:∀ x,Summable (fun i=>f i x)): X.Verse A fun x=>∑' i,f i x:=by
    intro i; simp_rw [Poly.share (he _)]
    refine Rune.assembly _ (fun j=> h j i) (fun z=>?_)
    exact ((he z).hasSum.map (Poly.get i).toLinearMap.toAddMonoidHom (Poly.part_cont i)).summable
end Verse
namespace Purchase
variable {ζ:V→Site n}(d:Taste (Dais T) ζ P R)
structure Draft : Prop where
    regular (i U):X.Rune (d.menu.rays i).val (d.menu.branch i) fun θ=>d.menu.regular θ i U
    unit i : X.Rune {i} {ζ i} fun θ=> d.menu.global θ i
    caption (i): X.Rune (d.tag i).val (d.site i) (fun θ=>d.score θ i)
structure Credit : Prop extends Draft X d where
    forced (i j U): X.Rune (d.menu.marks i j).val (P.activities.forced i).support fun θ=>d.menu.force θ i j U

variable {α:Type*}(F:Dais T→Feed G n R α)
-- uses Ledger F for fixed columns, expose ANY θ.
def Owes (v₀:Dais T):Prop:=∀ i U,X.Rune ((F v₀).mode i).val (Feed.region ((F v₀).column i)) (fun θ=> (F θ).value i U)
lemma verse {v₀:Dais T} (h:Owes X F v₀)(he:Ledger F)(hs:∀ z U,Summable (fun i=> (F z).value i U))(i:Column R n)(U:Config G n): X.Verse (Feed.region i) fun θ=>(F θ).slip i U:=by
    let c :={l:α // (F v₀).column l=i}
    let f(z:Dais T):ℂ:=∑' l:c,(F z).value l.val U
    have ht(z:Dais T):Summable fun l:c=> (F z).value l.val U:= (hs z U).comp_injective Subtype.val_injective
    have hg(i' : c) : X.Rune (Feed.domain i).val (Feed.region i) (fun z=> (F z).value i'.val U):=by have hz:=h i'.val U; unfold Feed.mode at hz; rw [i'.property] at hz; exact hz
    have h0:X.Rune (Feed.domain i).val (Feed.region i) f:=Rune.assembly _ hg ht
    have hf(z):(F z).row i U=f z:=by unfold Feed.row f c; rw [funext (he.column v₀ z)]; rfl
    unfold Feed.slip; split
    next hr=>simp_rw [hf]; exact Verse.send _ h0
    next hE=>
        simp_rw [hf]
        have hl(z): f z=f v₀:=h0.plays.stay _ _ (by rw [show Feed.domain i=R.quiet from not_ne_iff.mp hE]; exact fun i h=> (notMem_empty i h).elim)
        simp_rw [hl]; exact Verse.same _ _ (fun j hh=>by unfold Poly.bead; exact (Poly.part_send _ _ _).trans (if_neg hh))

lemma stock (h:Credit X d)(hs:∀ z i U,Summable (fun j=> ((d.leaf z).contents.tagged i j U)))(i:ℕ)(U:Config G n): X.Verse (P.activities.forced i).support fun z=>(d.leaf z).contents.each i U:=
    Verse.sum (Verse.send _ (Rune.const _ _)) (Verse.assembly _ (fun j=> Verse.send _ (h.forced i j U)) (fun z=> hs z i U))

variable {μ ι:Type*}{S:Shelf G n ι μ}{p:BudgetPoint}(A:Dais T→ S.Stock p R ζ)
lemma merged (h:∀ i U,X.Verse (S.frame.read i) fun z=>(A z).ink i U)(i:S.Patch)(U:Config G n):X.Verse (Shelf.Stock.cargoAddr S p i).support fun z=>(stamp (A z)).flow i U:=by
    unfold stamp Shelf.Stock.cargo Letters.Frame.merged; dsimp only; split
    · exact Verse.prod (S.frame.letters i) (fun j z=> (A z).ink j U) (fun j hj=> (h j U).soar (S.frame.entries_inside _ hj))
    exact Verse.still _
end Purchase
end Vine
end YM.RG3.Alpes
