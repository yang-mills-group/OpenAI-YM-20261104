import YM.OPE.Trunk.Default
/-! # Stocks on raw positions (without a previous ERA) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t':ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "Ξ"=> C.path.rep N p
namespace Plain
variable {φ:Z→ℕ}{A:I⊕Z→ℝ} {d:I⊕Z→ℕ}
variable {v: (i:I⊕Z)→ C.label (d i)}
    {g: (i:I⊕Z) → Extra.Histories.Music (C.labels.level (d i)) C.path N p}
    {x :ℕ→ℝ}
local notation "B"=> Site (C.side b p)
local notation "U!"=> extras C (p:=p) (m:=N) Z (u N)
abbrev origin (Q:Rhythm I)(S:Q.Loom)(φ:Z→ℕ): I⊕Z→ℕ:= Sum.elim (fun i=> S.launch (Q.age i)) φ
abbrev labelCost (C:Family G)(φ:I→ℕ)(A:I→ℝ)(d:I→ℕ)(i:I):= birthClock C (φ i) (d i) (A i)
def showAt (Q:Rhythm I)(S:Q.Loom)(C:Family G)(φ:Z→ℕ)(A:I⊕Z→ℝ)(d:I⊕Z→ℕ) (t:ℕ): ℕ→ Q.TypeAt Z t →ℝ := let P:= labelCost C (origin Q S φ) A d; width Q S C (P ∘ Sum.inl) (earn C φ (P ∘ Sum.inr)) t
local notation "j!"=> Q.limit+1
local notation "ψ"=> origin Q S φ
local notation "Q'"=> walletF Z (Q.fromAll j!)
local notation "ϑ"=> Q.TypeAt Z (j!)
-- ensure literal equality at cutoff in this cast.
def past (C: Family G)(d:I→ℕ)(N p:ℕ)(v:(i:I)→ C.label (d i))(u:I→Site (C.side N p))(i:I) := C.O N p (v i) (u i)
def planWord (C:Family G)(d:I⊕Z→ℕ)(N p:ℕ)(v:(i:I⊕Z)→ C.label (d i))(u:I→ Site (C.side N p))(Q:Rhythm I)(t:ℕ) : Q.TypeAt Z t → Config G (C.side N p)→ℂ:= grouped_X (past C d N p v (extras C (p:=p) (m:=N) Z u)) (walletF Z (Q.fromAll t))
local notation "Y'"=> planWord C d N p v (u N) Q
local notation "V'"=> showAt Q S C φ A d
section Fill
structure Strands (C:Family G){W r D} (L:LogPackage C W r D) (d:J→ℕ) (φ:J→ℕ)(A:J→ℝ)(b N p:ℕ) (v:(i:J)→ C.label (d i))(g: (i:J) → Extra.Histories.Music (C.labels.level (d i)) C.path N p): Prop where
    asset i: Studio.Series C W (waybill (C.path.levels)) D N p (d i) (g i)
    wake i: b ≤ φ i ∧ φ i ≤ N
    rooms i: C.ref (d i) ≤ φ i
    live i: 0<A i
    stamina i: Next.UVStress.quota C (d i) (φ i) N p (v i) ≤ A i
-- holds only to born , but ok for extra.Beta.Avoid type conflict j!. fix below
variable {s : Ward (Names (Site (C.side b p)) (Q.TypeAt Z (Q.limit+1)))}
    (F:Strands C L d (origin Q S φ) A b N p v g)
include U h F in
set_option maxHeartbeats 500000 in
lemma entrance (he: Trial s) (hp:Fintype.card I+ Fintype.card Z ≤ r N) : let D':=due Z Q S φ j!; ∃ P:∀ m, ϑ → Cup (C.path.rep N p m), Ledger Θ N s (Y' j!) P (motif Z Q u j!) D' (showAt Q S C φ A d j!) 1 D ∧ ∀ z:Z, let k:=(d (.inr z)); let q:=v (.inr z); Studio.Mantle C.path N p (φ z) (C.localSection k) (1,false) 0 (((g (.inr z)).tone (φ z)).plays ((C.factory k N p).terminal.symm q)) (P (φ z) (.inr z)):=by
    let j:=Q.limit+1; intro t'; let P' := walletF Z (Q.fromAll j); let p':= P'.twig; let t:= origin Q S φ ∘ p'; let u':= motif Z Q u j
    have hJ: Q.limit < j:= Nat.lt_succ_self _
    have h_t:t'=t:= by funext x; cases x with
                              | inr=> rfl
                              | inl i=> change due Z Q S φ j! (.inl i)=S.launch _; rw [due_unpaid φ ((Q.bounded i.val).trans_lt hJ)]; rfl
    have hS : S.below 0 ≤ N:= ((S.up_b Q (le_refl _)).trans (U.lasts (le_refl _))).le -- implicit Q.limit
    have hy:showAt Q S C φ A d j!= earn C t (fun i=> labelCost C (origin Q S φ) A d (p' i)):=by
       funext m v; cases v with
       | inl i=> unfold showAt; rw [piece_steps (h:= show Q.age i.val < j from (Q.bounded _).trans_lt hJ)]; rfl
       | inr i=>rfl
    let K:= Q.TypeAt Z j; let d':= (fun i:K=>d (p' i)); let a i:=A (p' i); let z(i):= (g (p' i)); let v'(i:K):C.label (d' i):= v (p' i); have hV(i : K): P'.Solo i:=by
       rintro (k|k) hk;
       · rcases i with i|i
         · have hx : Q.ticket k (j!)=i:= Sum.inl.inj hk; have hz:Q.chief k (j!)=k:= Q.end_piece ((Q.bounded k).trans_lt hJ); rw [← hx]; exact congr_arg (Sum.inl (β:=Z)) hz
         cases hk
       cases i; cases hk; exact congr_arg _ (Sum.inr.inj hk).symm
    let f:= past C d N p v (extras C (p:=p) (m:=N) Z (u N)); have he' : planWord C d N p v (u N) Q j = past C d' N p v' (motif Z Q u j N):=by
       funext i U; unfold planWord grouped_X; rw [show (walletF Z _).contents i= _ from (hV i).content,prod_singleton]; rfl
    have hh(i:ℕ)(a:K) : u' i a=(extras C (p:=p) (m:=i) Z (u i)) (p' a):=rfl
    have he'' (i) m (hx:t i ≤ m)(hu:m<N) : u' (m+1) i=((Y).clock.op m p).ratio.embed (u' m i):=by cases i; exact U.starts _ m hx hu; exact (((Y).clock.op m p).ratio.root.map_zero).symm
    obtain ⟨X,hA,hX⟩:= Book.enters L h d' a v' z (U.born.trans hS) (fun k=> F.wake (p' k)) (fun j=>F.asset (p' j)) he (fun i h hn j=> U.centerStep h hn j) (U.prices_at hS le_rfl _ Z hp j) (fun j=> F.rooms (p' j)) (fun j=> F.live (p' j)) (fun j=>F.stamina (p' j)) he''
    rw [h_t,hy,he']; exact ⟨X,hA,fun z=> hX (.inr z) ⟩
-- p pipeline.Fram with epoch.t.Weight & cost budget.Could issue single Step.C.Shape prototype.G.P.Lock.Mintpoint.
local notation "A'"=> (Q.TypeAt Z t)
variable {s₀: Ward (Names (Site (C.side b p)) (Q.TypeAt Z t))} {he:t ≤ t'} {Y₀:Finset ℕ}
    (G' : Q.Host t P s₀)(H' : Rates S L T Y₀ x)
def Ensemble (d:I⊕Z→ℕ)(φ:Z→ℕ)(v: (i:I⊕Z)→ C.label (d i))(g: (i:I⊕Z) → Extra.Histories.Music (C.labels.level (d i)) C.path N p)(P:∀ m:ℕ,Q.TypeAt Z t → Cup (C.path.rep N p m)): Prop:=∀ z:Z,Studio.Mantle C.path N p (φ z) (C.localSection (d (.inr z))) (1,false) 0 (((g (.inr z)).tone (φ z)).plays ((C.factory (d (.inr z)) N p).terminal.symm (v (.inr z)))) (P (φ z) (.inr z))
include F H' U h G'
lemma upper (he:t ≤ Q.limit+1) (hp:Fintype.card I+ Fintype.card Z ≤ T) (hq:C.ref 0 < b)(hG:G.Simple)(hη:∀ m,S.below 0 ≤ m→ T ≤ r m)
    (hx:∀ l, t ≤ l→ l ≤ Q.limit → ∀ i,φ i ≤ S.below l)(hE:∀ l,t ≤ l→l ≤ Q.limit → ∀ k,S.below l ≤ k→k ≤ N → ∀ i j,P i j→(Y|>.budget k).B^2 ≤ separation (u k i) 0) : ∃ G₀:∀ i, A' → Cup (Ξ i), Ledger Θ (laterEdge Q S N t) s₀ (Y' t) G₀ (motif Z Q u t) (due Z Q S φ t) (V' t) (x t) D ∧ Ensemble d φ v g G₀:=by
     let u':=Q.limit+1; let Ψ:= walletF Z (Q.fold he); let E:=pullback Ψ s₀; have ht:= G'.trans he; have hA:=U.born; have hv:= (S.up_b Q (le_refl Q.limit)).le.trans (U.screen.le); have hp_:= H'.price u' le_rfl
     obtain ⟨R₀,h₀,hψ⟩:= entrance U L h F (s:=E) (ht.lens) (hp.trans (hη _ hv)); have hr:Bowl S L (due Z Q S φ) (showAt Q S C φ A d) P b T p N u t u':=by
        refine ⟨fun k hk hv=> ?_⟩; let hK:=Nat.le_of_lt_succ hv; obtain ⟨Z',hZ⟩:= no_sign U L φ hA hK (fun j=> ⟨(F.wake (.inr j)).1,hx k hk hK j⟩) hp hη (hE k hk hK); exact ⟨warmSet Z Q k,Z',hZ,wakeShape _ _ hK⟩
     obtain ⟨F',hf,hY⟩:= transit (F:=Y' j!) (F':=R₀) U L h H' G' hq hG he hr (by rw [show laterEdge Q S N j!= N from if_neg (by omega)]; exact h₀.thinner hp_.have_ hp_.cost )
     have he' : grouped_X (planWord C d N p v (u N) Q u') Ψ= planWord C d N p v (u N) Q t:=by funext j U; exact ((Q.transShape Z he).group_prod ℂ (fun i=> (past C d N p v (extras C (p:=p) (m:=N) Z (u N)) i U)) j).symm
     refine ⟨F',he' ▸ hf,fun z=>?_⟩; rw [hY]; exact hψ z
end Fill
end Plain
end YM.OPE.Log.Trunk.Rhythm.Store
