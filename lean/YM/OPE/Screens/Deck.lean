import YM.OPE.Screens.Shuttle
/-!
# Bringing along many fields with a spatial pledge. Sublimit
against same matrix underwriting as inlet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake Rhythm.Store Rhythm Next.UVStress Spec Cards Payments
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {H l m k b N p A t t' q d e:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {F:Extraction.Order}{S:Table C.book}{P:Loom Q}(U: Final C F S)
local notation "μ!"=> C.S.a
local notation "L!"=> P.launch Q.limit
local notation "K"=> C.path.levels.budget
local notation "T!"=> C.S.gridPoint
variable {f f': Filter (ℕ×ℕ)}[f.NeBot] (h:f ≤ F.fuse)
variable {x:I→ Cover} {v:I→ C.book.Token}
    {W r' D'}(L:LogPackage C W r' D')
variable (hG:G.Simple) {c:ℕ→ℝ}{c':Finset ℕ}{Z':I→ℝ}
variable (R:Rates P L A c' c)(H':Canvas P C H b x)
local notation "v'"=> (fun j=> (v j).1)
local notation "m!"=> P.below 0
local notation "t!"=> P.below H
local notation "μ"=> P.launch
local notation "ν"=> discharged L P A c
local notation "η"=> provision L P A c
local notation "w'"=> Highest.base_price Q C P (fun i=>(v i).1) Z'
local notation "w!"=> batchClock C P v Z' H
local notation "ζ"=> (Highest.base_price Q C P (fun i=>(v i).1) Z' * Variant.widen P C H l e)
structure Dir (C:Family G)(S:Table C.book)(k b m d:ℕ)(a o :ℝ)(x:I→ Cover)(v:I→ C.book.Token)(φ:Filter (ℕ×ℕ))(z:C.label d):Prop where
    ready : ∃ (g:Filter (ℕ×ℕ))(p:I→ C.book.Token)(V: ReadLabel C p)(f:ℕ×ℕ→ C.label d), g.NeBot ∧ g ≤ φ ∧ Starts g S v p V ∧ Adoption C m a d z g f ∧ ∀ᶠ i:ℕ×ℕ in g, PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) o ((lobby x p V k - stampEntry d f) i.1 i.2)
structure SignDir (C:Family G)(S:Table C.book)(k b m j d e:ℕ)(a o a' o' : ℝ)(x:I→ Cover)(v:I→ C.book.Token)(s:Finset I)(φ:Filter (ℕ×ℕ))(z:C.label d)(y:C.label e):Prop where
    ready : ∃ (g: Filter (ℕ×ℕ))(p:I→ C.book.Token)(V:ReadLabel C p)(f:ℕ×ℕ→ C.label d)(f':ℕ×ℕ→ C.label e), g.NeBot ∧ g ≤ φ ∧ Starts g S v p V∧ Adoption C m a d z g f ∧ Adoption C j a' e y g f' ∧ ∀ᶠ i:ℕ×ℕ in g, let X:= bill x p V s k - stampEntry (C:=C) e f'; PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) o' (X i.1 i.2) ∧ PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) o ((X * bill x p V (univ\ s) k - stampEntry d f) i.1 i.2)
include h H' hG L R
local notation "U₀"=> Highest.base_price
abbrev rootBound (P:Loom Q)(t m b q A:ℕ) (c:ℕ→ℝ) (L:LogPackage C W r' D')(u:ℝ) := stakes C b q / road C (P.below t) m (discharged L P A c t m *u) q
abbrev capBound (P:Loom Q)(t m A:ℕ)(c:ℕ→ℝ)(L:LogPackage C W r' D')(u:ℝ):= 2*stampOut C (P.below t) m (provision L P A c t*u)
local notation "X'"=> Trunk.lens C (L!)
local notation "Zt"=> (capBound P 0 d A c L)
local notation "Zr"=> (rootBound P 0 d b q A c L)
local notation "mainPaid"=> (PaidAt C.S)
include U
lemma knock (hp:C.ref 0<b)(hu:C.ref d ≤ q)(hv:∀ j,8*‖T! (L!) (x j)‖ ≤ μ! b)(hf:Stock.Tabs.opens C.path.levels 1 b q)(hk:q ≤ m!)(hA:Fintype.card I+Fintype.card (C.labels.level d).Index ≤ A)(hr':∀ i≥ m!,A ≤ r' i)
   (he:∀ j,C.ref (v j).1 ≤ P.launch (Q.age j))(hS:∀ j,0< Z' j)(hX:∀ j,Pad C S v j (P.launch (Q.age j)) f (Z' j)) : ∃ z, Dir C S (L!) b (m!) d (capBound P 0 d A c L (w')) (rootBound P 0 d b q A c L (w')) x v f z:=by
    choose w V hw hW hT using (fun i=> show ∃ _ _ ,_ from hX i); let t(i:I): C.book.Token:=⟨(v i).1,w i⟩; let g: ReadLabel C t:=V; let f' := lobby x t g (P.launch Q.limit); let ε:= (Zt w'); let u:= (Zr w'); let z(i:ℕ×ℕ)(p:C.label d):Prop:= quota C d (m!) i.1 i.2 p≤ε∧mainPaid i.1 i.2 b (C.beta i.1 i.2) u (f' i.1 i.2-entering p i.1 i.2)
    have hh:= largeMesh F|>.mono_left h
    have hz:∀ᶠ i in f,∃ p,z i p:=by
       filter_upwards [(periods.mono_left h).eventually (H'.pose L), hh.eventually_gt_atTop (L!),eventually_all.mpr hT,eventually_all.mpr (fun i=> coming U h (x i) (hv i) (t i).1), coming0 U h b d] with i hi hk' hh ht hy; let X(i:ℕ×ℕ)(s:I):= V s i; let P':= X' i.2 x; have ht': L! < i.1:= hk'; let W' j:= C.O i.1 i.2 (d:=(t j).1) (V j i) (P' i.1 j); have hS':f' i.1 i.2=fun g:Config G (C.side i.1 i.2)=>∏ j,W' j g:=funext fun j=> lobbyL g ht'.le
       obtain ⟨p,hp,hn,hr⟩:= Highest.receipts (hi _ ht') L U.room.cutoff (fun i=>(v i).fst) (fun s=> V s i) Z' R hf hk hp hu hG hA hr' hS he hh
       refine ⟨p,hp,hn,Next.UVStress.minus ?_ (hy _ hn),hS'.symm ▸ hr⟩; rw [hS']; apply Interior.combines; intro j _; unfold W' P'; rw [gallery ht'.le]; exact ht j _ hn
    let z'(i):= if h:∃ p,z i p then Classical.choose h else 0; have he': ∀ᶠ i in f,z i (z' i):=hz.mono fun i hi=> (by unfold z'; rw [dif_pos hi]; exact hi.choose_spec); obtain ⟨f₁,y,hY,hΨ,hP⟩:= copy_stop U h (he'.mono fun _ h=> h.1) (hu.trans hk);
    exact ⟨y,f₁,t,g,z',hY,hΨ,⟨funext fun i=> congr_arg (fun x=> Sigma.mk (v i).1 x) (hw i),fun i=>(hW i).mono_left hΨ⟩,⟨(he'.mono fun i h=>h.1).filter_mono hΨ,hP⟩,(he'.mono fun i h=>h.2).filter_mono hΨ⟩
lemma both (hp:C.ref 0<b)(hu:C.ref d ≤ q)(hy:C.ref e ≤ q)(hx:e∈ c')(hv:∀ j,8*‖T! (L!) (x j)‖ ≤ μ! b)(hf:Stock.Tabs.opens C.path.levels 1 b q)(hk:q ≤ m!)(hA:Fintype.card I+Fintype.card ((C.labels.level d).Index⊕ (C.labels.level e).Index) ≤ A)(hr':∀ i≥ m!, A ≤ r' i)
   (he:∀ j,C.ref (v j).1 ≤ P.launch (Q.age j))(hS:∀ j,0< Z' j)(hX:∀ j,Pad C S v j (P.launch (Q.age j)) f (Z' j))
   (hV:Q.Strike H l)(hO: ∀ᶠ p:ℕ in atTop,∀ i:I,i∉ Q.focus H→∀ m,P.below H≤ m →((C.path.levels.budget m).B)^2≤ separation (Trunk.lens C (P.launch Q.limit) p x m i) 0) : ∃ z y, SignDir C S (L!) b (m!) (t!) d e (Zt ζ) (Zr ζ) (capBound P H e A c L (w!)) (rootBound P H e b q A c L (w!)) x v (Q.focus H) f z y:=by
    choose w V hw hW hT using (fun i=> show ∃ _ _ ,_ from hX i); let t(i:I):C.book.Token:=⟨(v i).1,w i⟩; let g: ReadLabel C t:=V; let f':=Shuttle.bill x t g (Q.focus H) (P.launch Q.limit); let θ:=Shuttle.bill x t g (univ\ Q.focus H) (P.launch Q.limit); let ε:= Zt ζ; let u:= Zr ζ; let ε':= capBound P H e A c L (w!); let u':=rootBound P H e b q A c L (w!)
    let z(i:ℕ×ℕ)(x:C.label e)(p:C.label d):Prop:= let X:= f' i.1 i.2-entering x i.1 i.2; quota C d (m!) i.1 i.2 p ≤ ε ∧ quota C e (t!) i.1 i.2 x ≤ ε'∧ mainPaid i.1 i.2 b (C.beta i.1 i.2) u' X ∧ mainPaid i.1 i.2 b (C.beta i.1 i.2) u (X*θ i.1 i.2-entering p i.1 i.2)
    have hh := largeMesh F|>.mono_left h; have hz:∀ᶠ i in f,∃ x p,z i x p:=by
       filter_upwards [(periods.mono_left h).eventually (H'.pose L), hh.eventually_gt_atTop (L!),eventually_all.mpr hT,eventually_all.mpr (fun i=> coming U h (x i) (hv i) (t i).1), coming0 U h b d, coming0 U h b e,(periods.mono_left h).eventually hO] with i hi hK hh ht hy' hA' hD; let X:= fun j:ℕ×ℕ=> Trunk.lens C (L!) j.2 x; let P' := X i; have ht': L! < i.1:= hK; let y(j:I):=V j i; let W' j:= C.O i.1 i.2 (d:=(t j).1) (y j) (P' i.1 j); let G'(s:Finset I)(g: Config G (C.side i.1 i.2)):=∏ j∈s,W' j g
       obtain ⟨z₁,z₀,hz₁,hz₀,hi',h₁,h₀⟩:= Variant.committed (hi _ ht') L U.room.cutoff hV v' y Z' R hf hk hp hu hy hx hG hA hr' hS he hh (fun k hk _ i hi=> hD i hi k hk)
       have hI (s: Finset I): Interior ((center C.S i.2 hi' 0).chamber 0) (G' s):= Interior.combines _ _ (fun j _=> (by unfold W' P' X; rw [gallery ht'.le]; exact ht j _ hi'))
       refine ⟨z₁,z₀,?_⟩; let f₁:= G' (Q.focus H); let f₂:= G' (univ\ Q.focus H); have hX': f' i.1 i.2=f₁:= funext fun j=> billL g _ ht'.le; dsimp only [z]; rw [hX',show θ i.1 i.2=f₂ from funext fun j=>billL g _ ht'.le]; have hp': Interior _ (f₁-entering z₁ i.1 i.2):=Next.UVStress.minus (hI _) (hA' _ hi'); exact ⟨hz₀,hz₁,⟨hi',hp',h₁⟩,hi',Next.UVStress.minus (hp'.times (hI _)) (hy' _ hi'), h₀⟩
    let y(i):= if h:∃ x p,z i x p then h.choose else 0; let x'(i):= if h:∃ p,z i (y i) p then h.choose else 0; have he': ∀ᶠ i in f,z i (y i) (x' i):=by
       filter_upwards [hz] with i hi; have hf:∃ p,z i (y i) p:= (by unfold y; rw [dif_pos hi]; exact hi.choose_spec); exact (show x' i=Classical.choose hf from dif_pos hf).symm ▸ hf.choose_spec
    obtain ⟨f₁,x₀,hY,hΨ,hP⟩:= copy_stop U h (he'.mono fun _ h=> h.1) (hu.trans hk); have hE:=he'.filter_mono hΨ; obtain ⟨f₂,y₀,hY',hΞ,hR⟩:=copy_stop U (hΨ.trans h) (hE.mono fun i h=> h.2.1) (hy.trans (hk.trans (P.le_below Q (Nat.zero_le H) hV.atMost))); have hE := hE.filter_mono hΞ
    refine ⟨x₀,y₀,f₂,t,g,x',y,hY',hΞ.trans hΨ,⟨funext fun i=> congr_arg (fun x=> Sigma.mk (v i).1 x) (hw i),fun i=>(hW i).mono_left (hΞ.trans hΨ)⟩,⟨hE.mono fun _ h=>h.1,hP.mono_left hΞ⟩,⟨hE.mono (fun _ h=>h.2.1),hR⟩,?_⟩
    exact hE.mono fun i he=>he.2.2
end YM.OPE.Log.Trunk.Shuttle
