import YM.OPE.Trunk.Opening
/-!
# Advance through any stretch, till erasure

Given a mask already allowing the planned future superpositions,
and records since the newest point.All log budgets. No caloric overhead
seen in a single stack.Uniform over all matching selections genuinely
with these costs. -/
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
local notation "K"=> C.path.levels.budget
local notation "B"=> Site (C.side b p)
variable {p₀:Finset (Q.TypeAt Z t)} {φ:∀ i:ℕ,Q.TypeAt Z i→ℕ} {s': Ward (Names (Site (C.side b p)) (Q.TypeAt Z t))}
variable {F: Q.TypeAt Z t' → Config G (C.side N p)→ℂ}
    {F':∀ i:ℕ,Q.TypeAt Z t'→Cup (C.path.rep N p i)} {w:∀ t:ℕ,ℕ→ (Q.TypeAt Z t) →ℝ}
    {x:ℕ→ℝ}{e:t ≤ t'}
local notation "j!"=> laterEdge Q S N
local notation "ν"=> motif Z Q u
abbrev provision (S: Q.Loom)(T:ℕ)(x:ℕ→ℝ)(t:ℕ):= platform L T (S.below t) (S.launch t) (x (t+1))
abbrev transact (S: Q.Loom)(T:ℕ)(x:ℕ→ℝ)(t:ℕ):= debit L T (S.below t) (S.launch t) (x (t+1))
abbrev discharged (S:Q.Loom) (T:ℕ) (x:ℕ→ℝ) (t d:ℕ) := Tariff.signedT C (S.below t) d (transact L S T x t) (provision L S T x t)
-- cash reserves (every used sign degree d must belong to commissioned set)
structure Rates (S:Q.Loom)(L: LogPackage C W r D)(T:ℕ) (Y':Finset ℕ)(x:ℕ→ℝ): Prop where
     price t:t ≤ Q.limit+1 → Cash (x t)
     drip t:t ≤ Q.limit → x t ≤ transact L S T x t
     salute t d : t ≤ Q.limit → d∈Y' → x t ≤ discharged L S T x t d
variable {L}
structure Bowl (S:Q.Loom) (L: LogPackage C W r D)(φ:∀ i:ℕ,Q.TypeAt Z i→ℕ)(w:∀ t:ℕ,ℕ→(Q.TypeAt Z t)→ℝ) (P:I→ Z→Prop) (b T p N:ℕ) (u:∀ i:ℕ,I→ Site (C.side i p)) (l v:ℕ) : Prop where
    works t:l ≤ t→t < v → ∃ p₀:Finset (Q.TypeAt Z t),∃ U':Store.Case Q S L u N T t P p₀ (φ (t+1)),Store.Plans U' b (φ t)∧ w t=afterWidth (w (t+1)) (S.below t) (walletF Z (Q.fold t.le_succ)) p₀
variable (L) {s : Finset ℕ} (hR:Rates S L T s x) (V': Q.Host t P s')
lemma special (Q:Rhythm I)(Z:Type)(t:ℕ): walletF Z (Q.fold (le_refl t))=Fibers.same _:=by
    cases hB: walletF Z (Q.fold (le_refl t)) with | mk x y H=>
    have hb : x=id:=funext (fun q=>by cases q with
                  | inr z=>rw [show x _=_ from congr_arg (fun A=> A.bunch (.inr z)) hB.symm]; rfl
                  | inl p=>rw [show x _=_ from congr_arg (fun A=> A.bunch (.inl p)) hB.symm]; exact congr_arg Sum.inl (Q.valent p))
    subst x; have hx:y=id:=funext fun i=> H i; subst y; rfl
lemma label_self (G:Type)[CommMonoid G](q:J→G)(k:J): ∏ i∈(Fibers.same J).contents k,q i= q k:= by rw [show (Fibers.same J).contents k={k} from (show (Fibers.same J).Solo k from fun i h=> h.symm).content,prod_singleton]
include U L h V' hR
lemma transit (he:C.ref 0 < b) (hG:G.Simple)(e':t ≤ t') (B': Bowl S L φ w P b T p N u t t')(A: Ledger Θ (j! t') (pullback (walletF Z (Q.fold e')) s') F F' (ν t') (φ t') (w t') (x t') D) : ∃ F₀:∀ m:ℕ,Q.TypeAt Z t → Cup (C.path.rep N p m), Ledger Θ (j! t) s' (grouped_X F (walletF Z (Q.fold e'))) F₀ (ν t) (φ t) (w t) (x t) D ∧ ∀ i:Z,∀ m,F₀ m (.inr i)=F' m (.inr i):=by
    induction e' using Nat.decreasingInduction with
    | self=> refine ⟨F',?_, fun _ _=> rfl⟩; rw [special,pull_same] at A; rw [special, show grouped_X F (Fibers.same _)= F from (by funext i g; exact label_self ℂ (fun i=>F i g) _)]; exact A
    | of_succ i hi IH=>
       let A'_:= Q.fold i.le_succ; let Q':=walletF Z A'_; let Q'' :=walletF Z (Q.fold hi); have h_T:= Q.transShape_panel Z i.le_succ hi; let M:= pullback Q' s'; have hv: Q.Host (i+1) P M:=V'.trans i.le_succ
       obtain ⟨Θκ,hΘκ,hP⟩:= IH (V':=hv) (s':=M) (B':=⟨fun t h hv=> B'.works t (i.le_succ.trans h) hv⟩) (A:=h_T.wardrobe s'|>.symm ▸ A) -- named Θκ conflict notation etc
       obtain ⟨p₀,U',H',hW⟩:=B'.works i le_rfl hi
       obtain ⟨v,hV,hK,hL⟩:= Plans.pedant (d:=fun _=>0) (U:=U) L h U' hΘκ V' H' he hG (fun k _=>he.le.trans (U.atleast U'.tall)) (fun k hu=> (hu rfl).elim)
       rw [← hW] at hV
       have hf: grouped_X (grouped_X F (walletF Z (Q.fold hi))) Q'=grouped_X F (walletF Z (Q.fold hi.le)):=funext fun i=>funext fun g=> (h_T.group_prod ℂ (fun i=> F i g) i).symm
       rw [laterEdge,if_pos U'.tall,← hf]; exact ⟨v,hV.thinner (hR.price i (U'.tall.trans Q.limit.le_succ)|>.have_) (hR.drip i U'.tall),fun i m=> (hK _ (U'.onCrew i) m).trans (hP i m)⟩
end YM.OPE.Log.Trunk.Rhythm.Store
