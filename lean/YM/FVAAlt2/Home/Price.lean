import YM.FVAAlt2.Home.Read
/-!
# Matrices going from unadjusted Wilson→ MS and crossing bases before field conversion

`mix` is the compatible mark-array action. use REAL PS implementation first.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Set Finset Filter Topology Lattice
open FormalOPE FormalOPE.RG10.InversionTop
open Labels Extra.FD Maxwell
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Mixed PertExtension.Position
open Precision
open MeasureTheory MS MS.Koszul MS.Menus MS.Book MS.Tone MS.Vista
open MS.Tide MS.Local.Physical
open PowerSeries (C coeff constantCoeff)
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {G:Gauge}{L:Frames G}{B: Deck G}{h n m:ℕ}
set_option linter.unusedSectionVars false
local notation "S"=> PowerSeries ℝ
local notation "A"=> PowerSeries ℂ
-- general inserted arrays.
abbrev Datum (I:Type*) := Mark I PertExtension.Physical.Profile.n
local notation "ι" i => Fin (PertExtension.Physical.Profile.n i)
section algebra
variable {X Y Z R R': Type*}[Fintype X][Fintype Y][Fintype Z][CommSemiring R][CommSemiring R']

def mix (f:Datum X→R)(a:Matrix Y X R)(p:Datum Y): R:= ∑ i:Fin p.fst.n→X,f ⟨p.fst,i⟩* ∏ j,a (p.2 j) (i j)
lemma mixSame (f:Datum X→R) (a:Matrix X X R): PertExtension.Position.insert _ _ f a=mix f a := rfl
lemma mix1 [DecidableEq X] (f:Datum X→R): mix f 1=f := by funext p; convert! insert_one f p using 4; simp [Matrix.one_apply] -- maybe too many
lemma mixPap (K:R→+*R')(f:Datum X→R) (a: Matrix Y X R): K ∘ mix f a= mix (K ∘ f) (a.map K):= by funext x; simp [mix,Matrix.map_apply,map_prod]
lemma mix2 (f:Datum X→R)(a: Matrix Y X R) (b:Matrix Z Y R): mix (mix f a) b=mix f (b*a):= by
 funext p; let γ:=Fin (p.1.n); let μ:= p.2; let s:= p.1
 change (∑ i:Fin (s.n)→Y, (∑ j:Fin (s.n)→X, f ⟨s,j⟩ * ∏ k,a (i k) ( j k ))*∏ k,b ( μ k ) ( i k ))=_
 simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; unfold mix; apply Finset.sum_congr rfl; intro i _; simp_rw [Matrix.mul_apply]; rw [Fintype.prod_sum, Finset.mul_sum ]; exact sum_congr rfl fun j _=>by rw [Finset.prod_mul_distrib]; ring
lemma monoread (p:PertExtension.Physical.Profile) {U:Fin p.n→ Type*} [∀ i,Fintype (U i)](x:Fin p.n→Y)(L:Datum X→R)(b: Matrix Y X R)
    (J:(i:Fin p.n) →U i→ X)(h : ∀ i:Fin p.n, Injective (J i))(he:∀ i:Fin p.n, ∀ k:X, k∉ Set.range (J i) → b (x i) k=0): mix L b ⟨p,x⟩=∑ u:((i:Fin p.n)→U i), L ⟨p,(fun i=> J i (u i))⟩* ∏ i,b (x i) (J i (u i)):= by
 let f(t:(i:Fin p.n)→ U i): Fin p.n→X:= fun i=> J i ( t i ); let yaxs(w:Fin p.n→X):R:= L ⟨p,w⟩*∏ i,b (x i) ( w i )
 change ∑ i:Fin p.n→X, yaxs i= ∑ i,yaxs ( f i ); rw [ ← Finset.sum_image (f:=yaxs) (g:=f) ]; swap; exact (show Injective f from fun x y he=> funext (fun i=> h i (congr_fun he i) )).injOn
 symm; apply Finset.sum_subset (subset_univ _) ?_; intro i _ hi; have hm : ∃ j,i j ∉ Set.range (J j):= by
   by_contra! hz; choose K hK using hz; exact hi (mem_image.mpr ⟨ K,mem_univ _,funext hK⟩)
 obtain ⟨j,hj⟩:=hm; unfold yaxs; rw [Finset.prod_eq_zero (Finset.mem_univ j) (he j _ hj),mul_zero]
end algebra

variable (L B)
local notation "Ih"=> Glyph B h
local notation "Th"=> FormalOPE.RG10.Position.Deck L h
local notation "b" k=> mast B k L

-- commuting algebra inverses exactly.
private lemma stamp {V X Y:Type*}[AddCommGroup V][Module ℂ V][Fintype X][Fintype Y][DecidableEq X](K:Module.Basis X ℂ V)(P:Module.Basis Y ℂ V)(i j:X): (∑ k:Y,(P.repr (K i)) k * (K.repr (P k)) j)=if i=j then 1 else 0:=by
 have he:= congrArg (fun x=> K.repr x j) (P.sum_repr (K i)); simp only [map_sum,Finsupp.finsetSum_apply,map_smul, Finsupp.smul_apply,Module.Basis.repr_self,Finsupp.single_apply] at he; exact he

def Φin (L:Frames G)(B:Deck G)(h:ℕ):Matrix (Glyph B h) (RG10.Position.Deck L h) ℂ:=Ωc L B
def Φout (L:Frames G)(B:Deck G)(h:ℕ):Matrix (RG10.Position.Deck L h) (Glyph B h) ℂ:= Ωb L B
lemma Φlin : Φin L B h*Φout L B h=1:= by ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact stamp _ _ _ _
lemma Φlout : Φout L B h*Φin L B h=1:= by ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact stamp _ _ _ _

def din (L:Frames G)(B:Deck G)(h:ℕ):= (Φin L B h).map Complex.re
def dout (L:Frames G)(B:Deck G)(h:ℕ):=(Φout L B h).map Complex.re
@[simp] lemma din_at (i:Ih)(j:Th): (↑(din L B h i j):ℂ)= Ωc L B i j:= starc ..
@[simp] lemma dout_at (i:Ih)(j:Th): (↑(dout L B h j i):ℂ)= Ωb L B j i:= starb ..
lemma din_mul : din L B h*dout L B h=1:= by ext i j; apply Complex.ofReal_injective; simp_rw [ Matrix.mul_apply, Matrix.one_apply, Complex.ofReal_sum,Complex.ofReal_mul,din_at, dout_at ]; rw [apply_ite Complex.ofReal,Complex.ofReal_zero,Complex.ofReal_one]; exact stamp _ _ _ _
lemma dout_mul : dout L B h*din L B h=1:= by ext i j; apply Complex.ofReal_injective; simp_rw [ Matrix.mul_apply, Matrix.one_apply, Complex.ofReal_sum,Complex.ofReal_mul,din_at, dout_at ]; rw [apply_ite Complex.ofReal,Complex.ofReal_zero,Complex.ofReal_one]; exact stamp _ _ _ _

-- coherence entries (insert quantities don't depend on horizon used)
local notation "cR"=> PertExtension.Physical.Profile.n
variable {q:ℕ}
abbrev carryΩ (he:h ≤ q) := RG10.Position.Deck.climb L he
lemma raised_c(i:Ih)(x:Th)(he:h≤q): Ωc L B (up he i) (carryΩ L he x)= Ωc L B i x:= by
 let f:= RG10.Position.higher L he; let D:= RG10.Position.deck L h; let Q:=RG10.Position.deck L q; let t:= (b q).coord (up he i); let r:= carryΩ L he; have hx:i=i:= rfl;
 have hM:Fintype.card Ih≤Fintype.card (Glyph B q):=Fintype.card_le_of_injective _ (up_inj he); have hz : Injective r:= RG10.Position.Deck.climb_inj L he
 have hv := up_one (L:=L) he i; have hy : ∀ i:Th,f ( D i )= Q (r i ):= RG10.Position.cabin L he
 change Q.coord (r x) ((b q) _)= _; rw [ ← show f ((b h) i)=(b q) (up he i) from hv ];
 rw [ ← D.sum_repr (mast B h L i), map_sum,map_sum ]; simp_rw [map_smul, hy]; rw [Finset.sum_eq_single_of_mem x (by simp)]; · simp_rw [ Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_eq_same, smul_eq_mul,mul_one ];rfl
 intro i hi ha; rw [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_eq_of_ne (fun hh=> ha (hz hh.symm)),smul_zero]
lemma raised_b(i:Ih)(x:Th)(he:h≤q): Ωb L B (carryΩ L he x) (up he i)=Ωb L B x i:= by
 let M:= RG10.Position.deck L h; let K:= RG10.Position.deck L q; let f:= RG10.Position.higher L he; let r:= carryΩ L he
 have hz:= up_inj (B:=B) he; have hx:=RG10.Position.cabin L he x; have hv : ∀ j:Ih,f ((b h) j)=(b q) (up he j):= up_one (L:=L) he;
 change (b q).coord (up he i) (K (r x))= _; rw [ ← show f (M x)=_ from hx, ← (b h).sum_repr (M x), map_sum,map_sum ]; simp_rw [map_smul,hv]; rw [Finset.sum_eq_single_of_mem i (by simp)]; · simp_rw [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_eq_same,smul_eq_mul,mul_one];rfl
 intro a _ ha; rw [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_eq_of_ne (fun hh=>ha (hz hh.symm)),smul_zero]
end YM.FVAAlt2.Home
