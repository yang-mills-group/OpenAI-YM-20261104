import YM.RG3.Script.Marker

/-!
# Conservative engine: strand conservation by syntax BEFORE pricing

Partition output local exponent into registered short-hull entries vs not
edited; no restriction on width/order of the entries in algebra. Emit
actual masks on both sides and signed H/kernels, preserve captions also in
differences. Need supports and predicates already billed at this level or
use with pulls satisfying the conservation on all U directly. Fintype V but
possibly whole native-period reporting catalogue. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Edition
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary RG3.Law Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Estate Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {V:Type*} [Fintype V] [DecidableEq V]{R:Census V}{ζ:V→Site n}{G:Gauge}
  {e : Edition ζ R G} {A : Estate n R}

/-- Syntax addresses. U included globally with singleton support (if costs
use larger root/test connector, must use captions for it). -/
abbrev Reg (V : Type*) := ℕ ⊕ (ℕ ⊕ V) -- H,C,U
namespace Reg
def faces (e : Edition ζ R G) : Reg V → Support n := Sum.elim e.home (Sum.elim e.footer.cover fun i=> {ζ i})
def glyph (e:Edition ζ R G): Reg V→R.Mode := Sum.elim e.pins (Sum.elim e.footer.tag R.fire)
def values (e:Edition ζ R G): Reg V→ Config G n→ℂ := Sum.elim e.song (Sum.elim (fun i _=>e.footer.value i) fun i _=>e.pure i)
def lit : Reg V → Bool := Sum.elim (fun _=> true) (fun _=> false)
def bead (e:Edition ζ R G)(p:BudgetPoint)(U:Config G n)(i:Reg V):Poly R:= Poly.send (glyph e i) (if lit i then masked p.threshold (faces e i) (values e i) U else values e i U)
variable {p:BudgetPoint}{w:V→ℝ}{a u c Y : ℝ}{f:ℕ→ℝ}
lemma choir (U:Config G n) (hw:∀i,0<w i)(_h:e.Principle p)(he:e.Grant p w a u c Y f)(ha:p.supportExponent ≤ a):
    HasSum (bead e p U) (e.log p U):=by
  obtain ⟨hx,hy⟩:= living hw _h he ha U
  let l i:=Poly.send (e.footer.tag i) (e.footer.value i); let g(i:V):=Poly.send (R.fire i) (e.pure i)
  let F:=bead e p U
  let hg:Summable g:=(hasSum_fintype _).summable
  have ht:Summable (fun i=> F (.inr i)):=Summable.sum _ hy hg
  have hd:Summable F:=Summable.sum _ hx ht; rw [show e.log p U=tsum F from ?_];exact hd.hasSum
  rw [Summable.tsum_sum (f:=F) hx ht,Summable.tsum_sum (f:=fun i=>F (Sum.inr i)) hy hg, tsum_fintype (f:=fun (j:V)=>F (Sum.inr (Sum.inr j)))]; unfold log; change (∑ i:V,g i)+ _+tsum l=(∑' i:ℕ,e.birth p i U)+ (tsum l+∑ i:V,g i); abel
  
end Reg

structure Crew (V : Type*) where
  book : Reg V → Bool

def rbl {α:Type*}[Zero α](h:Bool)(a:α):α:=if h then a else 0

def keep (e:Edition ζ R G)(c:Crew V):Edition ζ R G:={
   e with pure:=fun s=> rbl (!(c.book (.inr (.inr s)))) (e.pure s)
          song:= fun i=>rbl (!(c.book (.inl i))) (e.song i)
          footer:= {e.footer with value:=fun i=>rbl (!(c.book (.inr (.inl i)))) (e.footer.value i)}}

section parse
variable (e : Edition ζ R G)(S:Crew V)(A : Estate n R)
/-- Register only those moving. -/
abbrev Public := {i:Reg V// S.book i=true}
instance count (S:Crew V):Countable (Public S):=by unfold Public Reg; infer_instance
structure Size where
  item : Public S→ℕ
  centered i : Reg.glyph e i.val=A.style (item i)
  growth i: Reg.faces e i.val⊆ A.region (item i)

variable {A e S}(s:Size e S A)
def cutting : A.Truss (Public S) G:= ⟨s.item,Reg.faces e ∘ Subtype.val,Reg.lit ∘ Subtype.val,Reg.values e ∘ Subtype.val,s.growth⟩
omit [Fintype V] in
lemma colored (p:BudgetPoint)(h:e.Principle p): (cutting s).Laws ζ:= by
  let T:=(cutting s)
  have ht i : LocalOn ↑(T.notice i) (T.song i) ∧ Measurable (T.song i) ∧ GaugeInvariant (T.song i) ∧ ∀ j∈(Reg.glyph e i.val).val,ζ j∈T.notice i:= by
    rcases i with ⟨i|(i|i),hi⟩
    · exact ⟨(h.reg i).sites,(h.reg i).borel,(h.reg i).symmetry,h.rem i⟩
    · exact ⟨(fun _ _ _=>rfl),measurable_const,fun _ _=>rfl,h.vertical.pins i⟩
    exact ⟨(fun _ _ _=>rfl),measurable_const,fun _ _=>rfl,fun j hj=> mem_singleton.mpr (congrArg _ (mem_singleton.mp hj))⟩
  refine ⟨fun i=>(ht i).1,fun i=>(ht i).2.1,fun i=>(ht i).2.2.1,fun i _ j _ hj=>?_⟩ -- fix
  apply (ht i).2.2.2 _; rwa [s.centered i]

omit [Fintype V] in
lemma cutfit (p:BudgetPoint)(U:Config G n)(i:Public S): ((cutting s).strand p).reel i U=Reg.bead e p U i.val:= by
  unfold RG3.Render.Stage.Trace.reel Reg.bead
  rcases i with ⟨i,he⟩
  rw [s.centered (⟨i,he⟩ : Public S)]; cases i with
  | inl _=> rfl
  | inr i=>cases i <;>rfl

omit [Fintype V] in
lemma keepsVal (p:BudgetPoint)(i:Reg V)(hh:S.book i=false) (U:Config G n) : Reg.bead (keep e S) p U i=Reg.bead e p U i:= by
  rcases i with i|(i|i)
  · change Poly.send _ (masked _ _ _ _)=_
    rw [show (Reg.values (keep e S) (Sum.inl i))=e.song i by simp only [Reg.values,Sum.elim_inl,keep,hh,rbl]; rfl]
    rfl
  · change Poly.send (e.footer.tag i) (rbl (!S.book (.inr (.inl i))) (e.footer.value i))=_; rw [hh];rfl
  change Poly.send (R.fire i) (rbl (!S.book (.inr (.inr i))) (e.pure i))=_; rw [hh];rfl
omit [Fintype V] in
lemma keeps_none (p:BudgetPoint)(i:Public S)(U:Config G n):Reg.bead (keep e S) p U i.val=0:= by
  rcases i with ⟨i|(i|i),he⟩
  · change Poly.send _ (masked _ _ _ U)=0
    rw [show Reg.values (keep e S) (.inl i)=0 from by simp only [Reg.values,Sum.elim_inl,keep,he,rbl]; rfl]
    unfold masked; simp
  · change Poly.send _ (rbl (!S.book (.inr (.inl i))) (e.footer.value i))=_; rw [he]; exact Poly.send_zero _
  change Poly.send _ (rbl (!S.book (.inr (.inr i))) (e.pure i))=_; rw [he]; exact Poly.send_zero _

variable {p:BudgetPoint}{w:V→ℝ}{a u c Y : ℝ}{f:ℕ→ℝ}
-- Charges either ignore motion or reissue with 0 cost; choose latter
def baseFee (S:Crew V) (f : ℕ→ℝ)(i:ℕ):= rbl (!(S.book (.inl i))) (f i)
omit [Fintype V] in
lemma keeps (e:Edition ζ R G)(S:Crew V)(h:e.Principle p): (keep e S).Principle p:= by
  refine ⟨h.hot,h.rem,fun i=>?_,⟨h.vertical.card,h.vertical.pins⟩⟩
  change p.Regular _ (rbl _ _); unfold rbl; split; exact h.reg _; exact Push.Local.regular_const _
omit [Fintype V] in
lemma keep_price (S:Crew V)(hw:∀i,0<w i)(_h:e.Principle p)(he:e.Grant p w a u c Y f):(keep e S).Grant p w a u c Y (baseFee S f):=by
  have hv i : 0≤baseFee S f i:=by unfold baseFee rbl; split; exact he.nn _;exact le_rfl
  refine ⟨fun i=>?_,hv,fun i j hj=>?_,fun i=>budget_mono (he.more i) ?_ ?_,fun i=> budget_mono (he.captions i) ?_ ?_⟩
  · unfold keep; dsimp only; unfold rbl; split; exact he.one _; rw [norm_zero,mul_zero];exact (mul_nonneg (hw _).le (norm_nonneg _)).trans (he.one i)
  · unfold keep baseFee rbl; simp only;split; exact he.pay i j hj; simpa using! (Push.Local.bound_const (X:=e.home i) (o:=ζ j) (B:=p) (G:=G) 0)
  · exact fun _=> per_nn (fun i=>(hw i).le) hv _ _
  · intro j; unfold per keep; dsimp only; split_ifs; swap; rfl
    unfold baseFee rbl expense; split; rfl
    rw [mul_zero,mul_zero]; exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (he.nn j))
  · exact fun _=> per_nn (fun i=>(hw i).le) (fun _=>norm_nonneg _) _ _
  intro j; unfold per keep; dsimp only; split_ifs; swap; rfl
  unfold rbl expense; split; rfl
  rw [norm_zero,mul_zero,mul_zero]; exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))


lemma etch (U:Config G n)(hw:∀ i,0<w i)(h:e.Principle p)(he:e.Grant p w a u c Y f)(ha:p.supportExponent ≤ a):
    e.log p U=(e.keep S).log p U+((cutting s).strand p).tally U:= by
  let t:=((cutting s).strand p); let F i:=t.reel i U
  let e':= e.keep S
  let hA i:= Reg.bead e p U i; let hB i :=Reg.bead e' p U i
  have hi (i:Reg V)(hh:¬(S.book i : Prop)):hA i-hB i=0:= sub_eq_zero.mpr (keepsVal p i (Bool.eq_false_iff.mpr hh) U).symm
  have ht (i:Public S):hA i.val-hB i.val=F i:=by rw [show hB _=_ from keeps_none p i U,sub_zero]; exact (cutfit s p U i).symm
  have hs:=Reg.choir U hw h he ha
  have hs':=Reg.choir U hw (keeps e S h) (keep_price S hw h he) ha
  have hx : (∑' i:Public S,F i)=e.log p U-(e.keep S).log p U:= by
    simp_rw [← ht]
    change (∑' i : {x:Reg V//(S.book x:Prop)},(hA-hB) i.val)=_
    erw [tsum_subtype ({x:Reg V|(S.book x:Prop)}:Set (Reg V)) (hA-hB),Set.indicator_eq_self.mpr (fun _ a=> ?_)]; swap -- obligation Support subset or indicator?
    · by_contra H; apply a; exact hi _ H
    exact (hs.sub hs').tsum_eq
  change _= _+tsum F
  rw [hx]; abel
end parse
end YM.RG3.Script.Edition
