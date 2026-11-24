import YM.FVAAlt2.Home.Lofty
/-!
# Basis at arbitrary reusable heights. `Loft` and `Plan` choices in the
 public RG10 position constructor accepted BEFORE ranks or requests. Provide
 REAL and complex arrays identifying exactly the same convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Finset Filter Topology Lattice Wilson Labels Source Source.Drops
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Native.Paint MS.Native.Wilsonian
open Extra.FD Maxwell Extraction
open FormalOPE
open FormalOPE.RG10.Position (Loft Plan)
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{d q:ℕ}{L:Frames G}{B:Deck G}
local notation "F"=> Labels.Label G d
local notation "V"=> Rake.Label B
set_option quotPrecheck false
local notation "ℜ" i=> (freeTable L).conj (table_spin L) i
local notation "W" d=> Table.Field (freeTable L) d

-- Injections need NOT be recertified per scale. Map one label to W.
def mast (B:MS.Local.Physical.Deck G)(d:ℕ)(L:Frames G): Module.Basis (Glyph B d) ℂ (Table.Field (freeTable L) d):= ( Daylight B d ).map (exactField L d).symm
abbrev peg (B:Deck G)(v:Glyph B d)(L:Frames G):= mast B d L v
def popTag (x:Rake.Label B): Label G x.h:= Shop.seat B x.item.2
def pegK (p:Rake.Label B)(L:Frames G): Table.Field (freeTable L) p.h := sourceAt L p.h (popTag p)
lemma pegK_owns (x : Glyph B d) : writes L x.size (pegK (Lobby.owner x) L)=observable G x.size (Shop.seat (d:=x.size) B x.2.2):= RG10.Position.form ..
lemma owned (v: Glyph B d) : peg B v L = RG10.Position.higher L (show v.size≤d from by unfold Glyph.size; exact Nat.le_of_lt_succ v.1.isLt) (pegK (Lobby.owner v) L) :=by
 apply writes_inj L d; rw [RG10.Position.writes_higher,pegK_owns]; unfold peg mast writes; rw [Module.Basis.map_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,readHeight];rfl
lemma pegFrame (i: Glyph B d): MvPolynomial.IsWeightedHomogeneous compileW (writes L d (peg B i L)) (i.size,i.grade):= by
 rw [owned (L:=L), RG10.Position.writes_higher,pegK_owns]; exact RG10.Position.purity i.size _ _ (Shop.isSeated ..)
lemma peg_bar (i:Glyph B d) : (ℜ d) (peg B i L)=peg B i L:=by
 apply writes_inj L d; rw [writes_bar,owned (L:=L),RG10.Position.writes_higher,pegK_owns, ← observe_bar, Shop.single_p]
lemma mx (v:MS.Land.Plaid B d): (Lobby.owner (MS.Land.read v))=(⟨d,v⟩: Rake.Label B):=rfl
lemma pegl (v:MS.Land.Plaid B d): peg B (MS.Land.read v) L=pegK ⟨d,v⟩ L:=by apply writes_inj L d; rw [owned, RG10.Position.writes_higher]; rfl
-- upper/lower embedding via Glyph. Extension unique defeq level. useful all sectors.
abbrev up (h:d≤q)(i:Glyph B d):Glyph B q:= ⟨ ⟨i.size, Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.1.isLt).trans h)⟩, i.snd⟩
lemma up_owner (h:d≤q)(i:Glyph B d): Lobby.owner (up h i)= Lobby.owner i:=rfl
lemma up_one (h:d≤q)(i:Glyph B d): RG10.Position.higher L h (peg B i L) = peg B (up h i) L:=by apply writes_inj L q; rw [RG10.Position.writes_higher,owned (L:=L) i, owned (L:=L) (up h i),RG10.Position.writes_higher,RG10.Position.writes_higher]; rfl
lemma up_inj(h:d≤q) : Function.Injective (@up G d q B h):=by
 rintro ⟨⟨a,e⟩,i⟩ ⟨⟨b,h⟩,j⟩ he; obtain ⟨e',h'⟩:= Sigma.mk.inj he; have hv:a=b:=congr_arg Fin.val e'; subst b; exact congr_arg _ (eq_of_heq h')

lemma metal_shell(p: Glyph B d)(x: W d)(m : ℕ×ℕ)(hm:m ≠ (p.size,p.grade))(hx:MvPolynomial.IsWeightedHomogeneous compileW (writes L d x) m) : (mast B d L).repr x p=0:=by
 -- projection argument line from FormalOPE.RG10.Position.Loft.grade_zero
 let b:= mast B d L; let M(i:Glyph B d):=(i.size,i.grade); let c(i:Glyph B d):= if m=M i then b.repr x i else 0
 have h(i:Glyph B d) : MvPolynomial.weightedHomogeneousComponent compileW m (writes L d (b i))=if m=M i then writes L d (b i) else 0:=MvPolynomial.weightedHomogeneousComponent_of_mem (pegFrame i)
 have he: ∑ i,c i • b i=x:=by
    apply writes_inj L d; obtain ht:=congr_arg ((MvPolynomial.weightedHomogeneousComponent compileW m) ∘ writes L d) (b.sum_repr x)
    rw [_root_.map_sum]; simp only [comp_apply,_root_.map_sum,hx.weightedHomogeneousComponent_same] at ht; rw [← ht]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,map_smul,map_smul,h i]; unfold c; split <;> simp
 change b.repr x p=_; suffices ht: (∀ i,b.repr x i=c i) by exact (ht p).trans (if_neg hm)
 let Yz(i : Glyph B d):=b.repr x i-c i
 have hz: ∑ i,Yz i • b i=0:=by unfold Yz; simp_rw [sub_smul, Finset.sum_sub_distrib,b.sum_repr,he,sub_self]

 exact fun i=> sub_eq_zero.mp (Fintype.linearIndependent_iff.mp b.linearIndependent Yz hz i)
set_option linter.unusedSectionVars false
lemma clBasis {U E:Type}[Fintype U] [AddCommGroup E][Module ℂ E](B:Module.Basis U ℂ E) (g: E→ₛₗ[starRingEnd ℂ] E)(h:∀ i,g (B i)=B i){x:E}(he:g x=x)(i:U): (↑((B.repr x i).re):ℂ) = B.repr x i:= by
 classical
 apply Complex.conj_eq_iff_re.mp
 have hf: ∑ k,(star (B.repr x k)) • B k=x:=by
    nth_rw 2 [← he]; conv_rhs=> rw [← B.sum_repr x,map_sum]
    exact sum_congr rfl fun k _=>by rw [map_smulₛₗ,h]; rfl
 have hu := congr_arg (fun y=> B.repr y i) hf; rw [map_sum,Finsupp.finsetSum_apply] at hu; simpa [map_smul,Finsupp.single_apply,mul_ite] using hu
-- literal owner-level cross (without rotations downstream)
variable (L)
open FormalOPE.RG10.Position (Spur)
local notation "Y"=> RG10.Position.Deck L d
variable (B)
-- full matrix at announced height, preserve both grades and real.
def Ωb (i: Y)(p:Glyph B d):ℂ:= (mast B d L).repr (RG10.Position.deck L d i) p
def Ωc (p:Glyph B d)(i:Y):ℂ:= (RG10.Position.deck L d).repr (mast B d L p) i
lemma starb(i:Y)(p:Glyph B d): (↑((Ωb L B i p).re):ℂ)=Ωb L B i p:=clBasis _ (ℜ d) (@peg_bar G d L B) (RG10.Position.deck_real L d i) p
lemma starc(p:Glyph B d)(i:Y): (↑((Ωc L B p i).re):ℂ)=Ωc L B p i:=clBasis _ (ℜ d) (RG10.Position.deck_real L d) (peg_bar p) i
lemma cite_b (p:Glyph B d)(i:Y)(h: RG10.Position.Deck.grades L d i≠(p.size,p.grade)): Ωb L B i p=0:= metal_shell _ _ _ h ( RG10.Position.grade_written L d i)
lemma cite_c (p:Glyph B d)(i:Y)(h: RG10.Position.Deck.grades L d i≠(p.size,p.grade)): Ωc L B p i=0:= RG10.Position.grade_zero L d i (Ne.symm h) (pegFrame p)
lemma tally_b(i:Y): ∑ x:Glyph B d,Ωb L B i x • mast B d L x=RG10.Position.deck L d i:=(mast B d L).sum_repr _
lemma tally_c(i:Glyph B d): ∑ x:Y,Ωc L B i x • RG10.Position.deck L d x=mast B d L i:=(RG10.Position.deck L d).sum_repr _

def realToken (i:Spur L d): Y:= ⟨⟨ d,Nat.lt_succ_self _ ⟩,i⟩
lemma charge_token (i:Spur L d): (RG10.Position.Deck.grades L d (realToken L i)).1=d:=rfl
lemma level_ident(i:Spur L d) : ∑ p : MS.Land.Plaid B d, Ωb L B (realToken L i) (MS.Land.read p) • (mast B d L) (MS.Land.read p)= RG10.Position.deck L d (realToken L i):=by
 have h:Function.Injective (MS.Land.read (B:=B) (d:=d)):=by intro i j he; exact eq_of_heq (Sigma.mk.inj he|>.2)
 let f:= fun x:Glyph B d=>Ωb L B (realToken L i) x • mast B d L x; change ∑ _, f _= _; rw [ ← Finset.sum_image (f:=f) (by exact h.injOn) ]; apply Eq.trans _ (tally_b L B (realToken L i)); apply Finset.sum_subset (Finset.subset_univ _); rintro ⟨⟨k,hk⟩,u⟩ _ hv
 have hu:k≠d:=by intro e; subst k; apply hv; exact Finset.mem_image.mpr ⟨ u,Finset.mem_univ _, rfl⟩
 let v: Glyph B d:=⟨⟨k,hk⟩,u⟩; change Ωb L B _ v • _=_; rw [cite_b L B v _ (fun e=> hu (charge_token L i ▸ congr_arg Prod.fst e.symm)), zero_smul]
lemma level_reverse(i:MS.Land.Plaid B d): ∑ k:Spur L d, Ωc L B (MS.Land.read i) (realToken L k) • RG10.Position.deck L d (realToken L k)= (mast B d L) (MS.Land.read i):=by
 have h:Function.Injective (realToken L (d:=d)):=fun _ _ he=> eq_of_heq (Sigma.mk.inj he|>.2)
 let f:= fun x:Y=>Ωc L B (MS.Land.read i) x • RG10.Position.deck L d x; rw [ ← Finset.sum_image (f:=f) (by exact h.injOn) ]; apply Eq.trans _ (tally_c L B (MS.Land.read i)); apply Finset.sum_subset (Finset.subset_univ _); rintro ⟨⟨k,hk⟩,u⟩ _ hv
 have hu:k≠d:=by intro e; subst k; apply hv; exact Finset.mem_image.mpr ⟨ u,Finset.mem_univ _, rfl⟩
 unfold f; rw [cite_c L B (MS.Land.read i) ⟨⟨k,hk⟩,u⟩ (fun e=> hu (congr_arg Prod.fst e)), zero_smul] -- k defeq
end YM.FVAAlt2.Home
