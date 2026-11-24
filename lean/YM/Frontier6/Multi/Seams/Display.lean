import YM.Frontier6.Multi.Tale.Letters

/-!
# On the joint actual programs: compute a single exterior reading at once

No multiplicativity of states at separated positions! Expand in the exact list,
slots symmetric. Census assembled at one finer geometry level. Use distinct rows
also when charging mixtures of counter materials at cells.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G}{k m l N p:ℕ}

structure Plan (C: Family G) (P:Type)(f:P→Type) where
     point (i:P):f i→ Cover
     letter (i:P):f i→ C.book.Token
     fee : P→ℂ
variable {V P:Type}[DecidableEq V][Fintype V] {P':V→Type} {W': (i:V)→P' i→Type}
variable (X:∀ i:V,Plan C (P' i) (W' i)) [_i : ∀ i,Fintype (P' i)] [_j : ∀ i b,Fintype (W' i b)]
variable {F:Extraction.Order}{S: Table C.book}
set_option quotPrecheck false
local notation "ι"=> (∀ i:V,P' i)

namespace Plan
section single
variable {f:P→Type} [Fintype P] [∀ i,Fintype (f i)]
def cost (X: Plan C P f) (k N p:ℕ)(U:Config G (C.side N p)) : ℂ:= ∑ i:P,X.fee i*∏ s:f i,C.O N p (X.letter i s).2 (Cells.location C.S k N p (X.point i s)) U
def syntaxR (X:Plan C P f)(k:ℕ)(c:E4) (S:Table C.book) : Spelling S:=∑ i,X.fee i • assembly S (fun s=> C.S.gridPoint k (X.point i s)+c) (S.classTokens ∘ X.letter i)
end single
-- Integer labels via sigma grid absolutely aligned cutoff.
def relationRow (x: ι) : ℂ:=∏ i:V, (X i).fee (x i)
abbrev Slots (x:ι):= Σ i:V, W' i (x i)
def report (x:ι): Slots (W':=W') x→ C.book.Token:= fun i=> (X i.1).letter (x i.1) i.2

def landing (k:ℕ) (c:V→ E4)(x:ι):Slots (W':=W') x→ E4:=fun i=> C.S.gridPoint k ((X i.fst).point (x i.fst) i.snd)+c i.1
def fund (h:k ≤ m)(c:V→ Cover)(x:ι) : Slots (W':=W') x→ Cover:=fun i=> pushSite C.S h ((X i.fst).point (x i.fst) i.snd)+c i.1
def draw (k:ℕ)(c:V→ E4)(x:ι): Spelling S:= assembly S (landing X k c x) (S.classTokens∘ report X x)
lemma route (k:ℕ)(S:Table C.book)(c:V→ E4) : ∏ i:V,(X i).syntaxR k (c i) S= ∑ x:ι, relationRow X x • draw (S:=S) X k c x:=by
    unfold syntaxR; rw [Tale.muls]; apply Finset.sum_congr rfl; intro x _; apply congr_arg (relationRow X x • ·); exact (concatenate_many S (fun i:V=>fun s=>C.S.gridPoint k ((X i).point (x i) s)+c i) (fun i=>S.classTokens∘ (X i).letter (x i))).symm

lemma gridded (h:k ≤ m)(c:V→ Cover)(x:ι)(i:Slots (W':=W') x) : C.S.gridPoint m (fund X h c x i)=landing X k (C.S.gridPoint m ∘ c) x i:=by unfold fund; rw [Work.B16.grid_add,finer]; rfl

local notation "W"=> Slots (W':=W')
lemma rates (c:V→ Cover)(x:ι)(h:k ≤ m)(he:m ≤ N)(u:Config G (C.side N p)) : (∏ i:V, ∏ j:W' i (x i), C.O N p ((X i).letter (x i) j).2 (Cells.location C.S k N p ((X i).point (x i) j)) (Lattice.translate (Cells.location C.S m N p (c i)) u))= ∏ i:W x, C.O N p (report X x i).2 (Cells.location C.S m N p (fund X h c x i)) u:=by
   rw [Fintype.prod_sigma]; apply Finset.prod_congr rfl; intro i _; apply Finset.prod_congr rfl; intro j _; rw [C.translation];
   unfold fund; dsimp only; rw [Extraction.Order.location_add,location_down _ h he]; rfl
lemma sheet (c:V→ Cover)(h:k ≤ m)(he:m ≤ N)(u:Config G (C.side N p)) : ∏ i:V, (X i).cost k N p (Lattice.translate (Cells.location C.S m N p (c i)) u)=∑ x:ι, relationRow X x * ∏ i:W x, C.O N p (report X x i).2 (Cells.location C.S m N p (fund X h c x i)) u:=by
   unfold cost; rw [Fintype.prod_sum]; simp_rw [← rates X c _ h he u, Finset.prod_mul_distrib]; rfl

-- needle generic requirement
variable (c:V→ Cover)(h:k ≤ m)
variable (hG:∀ x:∀ i:V,P' i,∀ a:Axis,Injective (fun i:Slots (W':=W') x=>landing X k (C.S.gridPoint m ∘ c) x i a))
local notation "M"=> Fintype.card ι
local notation "E"=> (Fintype.equivFin ι).symm
local notation "e"=> (fun x:ι=> (Fintype.equivFin (W x)).symm)
local notation "N'"=>fun i:Fin (M)=> Fintype.card (W ((E) i))
local notation "Y"=>(fun i:Fin (M)=> fund X h c ((E) i) ∘ (e ((E) i)))
local notation "U"=>(fun i:Fin (M)=> report X ((E) i) ∘ (e ((E) i)))

def aerials (F:Extraction.Order) : Episode C F m:= Platform.stillStory (C:=C) F M m (relationRow X ∘ (E)) (N') Y U (fun i=>by
   intro a; have hz:Extraction.Order.grid C m (Y i)=points (fun j=> landing X k (C.S.gridPoint m ∘ c) ((E) i) (e ((E) i) j)):=by ext1 j; exact gridded ..
   rw [hz]; exact (hG _ a).comp (e ((E) i)).injective)
local notation "R"=> aerials X c h hG F -- arg order check
include hG
lemma flows (he:m ≤ N) (u:Config G (C.side N p)) : (aerials X c h hG F).cuts N p 0 u= ∏ i:V, (X i).cost k N p (Lattice.translate (Cells.location C.S m N p (c i)) u):=by
   rw [sheet _ _ h he]; unfold Episode.cuts;
   rw [← Equiv.sum_comp (E)]; refine Finset.sum_congr rfl fun i _=>?_ ; apply congr_arg ( (R).factor i * ·)
   change (∏ j:Fin (N' i), C.O N p ((U) i j).2 (Cells.location C.S m N p ((Y) i j+0)) u)=_
   simp_rw [add_zero]; exact Equiv.prod_comp (e ((E) i)) (fun j=> C.O N p (report X ((E) i) j).2 (Cells.location C.S m N p (fund X h c ((E) i) j)) u)
lemma open_read (K:Final C F S)(s:StateIndex K) : fieldWord (aerials X c h hG F) (state K s)=poll S (state K s) (∏ i:V,(X i).syntaxR k (C.S.gridPoint m (c i)) S):=by
   let Q:= state K s; let f i:= (X i).syntaxR k (C.S.gridPoint m (c i)) S; rw [route,map_sum]; unfold fieldWord; rw [← Equiv.sum_comp (E)]; refine Finset.sum_congr rfl fun i _=>?_; rw [map_smul]; change (R).factor i*_=(R).factor i*_ ; apply congr_arg ((R).factor i*·)
   let y:ι:= E i; let p:= Extraction.Order.grid C m (Y i); let x:= landing X k (C.S.gridPoint m ∘ c) y
   have ht:Injective x:= fun i j he=> hG y 0 (congr_arg (fun t:E4=>t 0) he)
   have hp:WithLp.ofLp p=x∘ e y:= funext (fun j=> gridded X h c _ _)
   have hv:p∈conf _:=generic_conf _ ((R).gen i)
   change Q.expect (realize ((U) i) p) = poll S Q (assembly S x _); rw [Q.readAt, Tale.remap S Q x _ _ _ hp (hierarchy K s).laws.toSymmetric,if_pos ht]; change Q.read p (U i)=_; exact (S.at_project Q (hierarchy K s).laws.toSymmetric (respects K s) hv ((U) i)).symm

include h
lemma pays (K:Final C F S) (s:StateIndex K) (hr:Org.Grill C F) {ξ:Filter (ℕ×ℕ)}[ξ.NeBot](hf:ξ ≤ F.fuse)
    (hb:l ≤ m)(v:V→ Cover)(hv: Injective v)(π:V→ℝ) (r:V→ℕ)
    (hw:∀ i,0 ≤ π i) (hB:∀ i:V,l ≤ r i) (ht:∀ i:V,atStop C.S l (v i) (3*C.S.a (r i)) (C.S.gridPoint m (c i)))
    (hp:∀ x:V, ∀ᶠ i:ℕ×ℕ in ξ,∃ h:r x ≤ i.1,let T:=center C.S i.2 h 0; Interior (T.chamber 0) ((X x).cost k i.1 i.2) ∧ T.rootTest (C.beta i.1 i.2) ((X x).cost k i.1 i.2) ≤ π x) : ‖poll S (state K s) (∏ i:V,(X i).syntaxR k (C.S.gridPoint m (c i)) S)‖ ≤ ∏ i:V,π i:=by
   rw [← open_read X c h hG K s]; apply Platform.lectern K (R) v hv s hr hb hf π hw
   filter_upwards [eventually_all.mpr hp,Eventually.filter_mono hf (large_mesh F m)] with i hT hN
   obtain ⟨N,p⟩:=i; change m ≤ N at hN; let T:=center C.S p (hb.trans hN) 0
   choose hL g hH hv hY using fun i=> show ∃ (h:r i ≤ N)(g:Config G (C.side N p)→ℂ), Interior (T.chamber 0) g∧ T.rootTest (C.beta N p) g≤ π i ∧ T.copy (wrap T.period (v i)) g=(X i).cost k N p ∘ Lattice.translate (Cells.location C.S m N p (c i)) from ⟨(hT i).choose,moved_basis K.room.cutoff (hT i).choose (hB _) _ (hT i).choose_spec.1 (hT i).choose_spec.2 (at_margin C.S p _ _ hb hN (hT i).choose (ht i))⟩
   refine ⟨hb.trans hN,g,fun i=>⟨hH i,hv i⟩,funext fun u=>?_⟩; rw [flows X c h hG hN]; exact Finset.prod_congr rfl fun j _=> (congr_fun (hY j) u).symm
end Plan
end YM.Frontier6.Road
