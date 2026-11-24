import YM.OPE.Trunk.Tour
import YM.OPE.Laying.Tariff
/-!
# A stage opening. Spend, mint, roll or replace

Construct the one-motion step.Stamped prices at every use
with terms still shrinking while unactivated. Temporal bounds only
assumed from the same tour, not at disjoint layout origins. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t':ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
namespace Rhythm
variable (Q) (Z)
abbrev TypeAt (Q:Rhythm I) (J:Type) (t:ℕ):= Q.Panel t ⊕ J
abbrev motif (u:∀ i:ℕ,I→Site (C.side i p)) (t:ℕ) (m:ℕ) : TypeAt Q Z t → Site (C.side m p):= track Z Q (extras C (p:=p) (m:=m) Z (u m)) t
-- global width functions.Time(t)
def laterEdge (S:Q.Loom) (N t:ℕ):= if t ≤ Q.limit then S.below t else N
variable {Z} {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)} {U:Q.Tour C S b H N p u}
namespace Store
variable {Q} {W r D}(L:LogPackage C W r D)(h:C.Makes)
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "K"=> C.path.levels.budget
local notation "v!"=> Q.TypeAt Z t
local notation "z!"=> Q.TypeAt Z (t+1)
local notation "Φ"=> walletF Z (Q.fold t.le_succ)
local notation "b!"=> (S.below t)
local notation "B"=> Site (C.side b p)
variable {p₀:Finset (Q.TypeAt Z t)} {φ:Q.TypeAt Z (t+1)→ℕ} {s': Ward (Names (Site (C.side b p)) (Q.TypeAt Z t))}
-- robust opening assumptions before orbit.Same T number through all operations
structure Case (Q:Rhythm I) (S:Q.Loom)(L: LogPackage C W r D)(u:∀ i:ℕ,I→Site (C.side i p))(N T t:ℕ)(P:I→ Z→Prop)(p₀:Finset (Q.TypeAt Z t)) (φ:Q.TypeAt Z (t+1)→ℕ) : Prop where
    enough : Fintype.card I+Fintype.card Z ≤ T
    tall : t ≤ Q.limit
    count m : S.below 0≤ m→T≤ r m
    extra k : S.below t≤k→ k ≤ N → ∀ i j,P i j → (C.path.levels.budget k).B^2 ≤ separation (u k i) 0
    onCrew j:Sum.inr j∈ p₀
    owner (i:Q.Panel t): Sum.inl i∉p₀→ t ≤ Q.age i.val
    single i:i∈p₀→ (walletF Z (Q.fold (le_trans (le_refl t) (Nat.le_succ t)) )).Solo i
    manual (i): (walletF Z (Q.fold t.le_succ)).bunch i∈p₀ → φ i ≤ S.below t
    bleed (i) : (walletF Z (Q.fold t.le_succ)).bunch i∉p₀ → φ i=S.launch t

variable {F: Q.TypeAt Z (t+1) → Config G (C.side N p)→ℂ}
    {F':∀ i:ℕ,Q.TypeAt Z (t+1)→Cup (C.path.rep N p i)} {w:ℕ→ (Q.TypeAt Z (t+1)) →ℝ}
    {x y :ℝ}
local notation "j!"=> S.launch t
variable (U' : Case Q S L u N T t P p₀ φ)
    (A : Ledger (standC C b N p) (laterEdge Q S N (t+1)) (pullback (walletF Z (Q.fold t.le_succ)) s') F F' (motif (C:=C) Z Q u (t+1)) φ w x D)
    (J' : Q.Host t P s')
-- Pack stamina for Season motion.Arc. Cost drill orientation independent of ge.A.
include U U' J'
lemma clearance (he:C.ref 0 < b) : Book.Release Θ Φ p₀ s' b! j! L φ (motif Z Q u (t+1)) := by
    have ht:=U'.tall; have hv:= U'.enough; refine ⟨J'.lens,he,U.atleast ht,S.stair t ht,U'.single,U'.manual,U'.bleed,fun k he h=> ?_,fun k he h=> ?_,?_,?_⟩
    · have hX:= (S.le_below Q (Nat.zero_le _) ht).trans he; have hH := hv.trans (U'.count k hX); have hk: k<N:= h.trans_lt (U.lasts ht); exact ⟨U.prices_at hX hk.le _ Z hH _,U.prices_at (hX.trans k.le_succ) hk _ Z hH _⟩
    · have hk:= (S.le_below Q (Nat.zero_le _) ht).trans (Nat.le_of_succ_le he); have hh:= (h.trans_lt (U.lasts ht)).le; exact U.apartCost L J' t.le_succ hk hh (fun i hi=> (Q.launch_down S hi ht).le.trans (Nat.le_of_succ_le he)) (U'.extra k (Nat.le_of_succ_le he) hh)
    · rintro (i|i) (j|j) hi <;> try rfl
      exact U.coalescent t ht i.val j.val ((Q.seats ..).1 (Sum.inl.inj hi)); cases hi; cases hi
    rintro (i|i) hi; exact U.fully t ht i.val (U'.owner i hi); exact (hi (U'.onCrew i)).elim
include A h
lemma arrivesStep (he:C.ref 0 < b): Ledger Θ (S.launch t+1) (pullback Φ s') F F' (motif Z Q u (t+1)) φ w x D:=by
    have ht:= U'.tall; let m:= S.launch t; let s:= motif Z Q u (t+1); let b':= pullback Φ s'
    have hb:m<laterEdge Q S N (t+1):= by unfold laterEdge; split; rename_i he; exact S.upper _ he; exact U.lasts ht
    have h:t ≤ t+1:= t.le_succ; have hy:= U.born; have hψ(j : ℕ)(hj:m ≤ j) : S.below t ≤ j:= (Q.belowLaunch S ht).le.trans hj
    have hQ(j:ℕ)(hj:m ≤ j): S.below 0 ≤ j:= (S.le_below Q (Nat.zero_le _) ht).trans (hψ j hj)
    have hZ:= hQ (m+1) m.le_succ
    refine Ledger.steers L ‹C.Makes› A he.le (hy.trans hZ) hb ?_ ?_
    · intro i; by_cases hp:(Φ).bunch i ∈ p₀; · exact (U'.manual i hp).trans (hψ (m+1) m.le_succ)
      rw [U'.bleed i hp]; exact Nat.le_succ _
    intro j he hh; have hl:= m.le_succ.trans he; have hg:= hQ j hl; have h_B' := hh.trans_le A.limit; have hk:= U'.enough.trans (U'.count j hg); refine ⟨U.prices_at hg h_B'.le (r j) Z hk _, U.prices_at (hg.trans j.le_succ) h_B' (r j) Z hk _,?_⟩
    apply U.interspace L (J'.trans (Nat.le_succ t)) hg h_B'.le (fun i hi=> (S.mono Q (Nat.le_of_lt_succ hi) ht).trans hl) (U'.extra j (hψ _ hl) h_B'.le)
local notation "Ω"=> platform L T b! j! x
local notation "y!"=> debit L T b! j! x
local notation "z'!"=> afterWidth w b! Φ p₀
lemma arrivesForm (he:C.ref 0 < b)(hG:G.Simple)(d:Q.TypeAt Z t→ℕ)(hD:∀ i, i∉p₀→ C.ref (d i) ≤ b!) : ∃ F₀:∀ i,Q.TypeAt Z t→Cup (C.path.rep N p i), Ledger Θ b! s' (grouped_X F Φ) F₀ (motif Z Q u t) (afterGoal φ b! Φ p₀) (afterWidth w b! Φ p₀) y! D∧
    (∀ k∈p₀,∀ i,F₀ i k=F' i ((Φ).twig k))∧ ∀ k∉p₀, Minted C N p b! (d k) (Ω * z'! b! k) (motif Z Q u t b! k) (F₀ b! k):=by
    have hx:Cash x:=⟨A.rate.1,A.rate.2⟩; have ht:0 < T:= (lt_of_lt_of_le (b:=Fintype.card I) (Fintype.card_pos_iff.mpr ⟨Q.star⟩) ((Nat.le_add_right ..).trans U'.enough))
    have hm:= Q.belowLaunch S U'.tall; have h_H : Fintype.card (Q.TypeAt Z (t+1))≤ T:=(Q.ceiling Z _).trans U'.enough; have hP:=Tariff.amounts L hG ht hx hm; obtain ⟨hf,hL,hY,hC,hK,-⟩:= Tariff.checkOut L hG ht hx hm
    let X(i):=motif Z Q u (t+1) i; let s (i):= X i ∘ (Φ).twig; have hζ:s=motif Z Q u t:=funext fun m=> Q.spent Z t.le_succ (u m) (fun _=>0) -- order
    obtain ⟨p₁,hp,hΩ,hΨ⟩:= Book.Release.issue L h (arrivesStep (U:=U) L h U' A J' he) (clearance (U:=U) L U' J' he) d ht h_H hG hD hP.1.have_ (show Ω ≤ _ from le_rfl) hP.2 hf.have_ hL.le hY.have_ hC (hK.trans hP.2)
    refine ⟨p₁, hζ ▸ hp,hΩ,fun k he=>?_⟩ -- defeq
    rw [← hζ,afterWidth,if_neg he]; exact hΨ k he
-- rolls all not flagged from arrivals before any sign call
local notation "s'!"=> motif Z Q u t
variable {L}
structure Plans (U':Case Q S L u N T t P p₀ φ) (b:ℕ) (φ':Q.TypeAt Z t→ℕ) : Prop where
    fund i : b ≤ φ' i
    terms k : k∈p₀→ φ' k= φ ((walletF Z (Q.fold t.le_succ)).twig k)
    max k:k∉p₀→ φ' k ≤ S.below t
    located k:k∉p₀→ ∀ m,φ' k≤ m → m < S.below t → motif Z Q u t (m+1) k=(Y|>.clock.op m p).ratio.embed (motif Z Q u t m k)
variable (L)
lemma Plans.pedant {d:Q.TypeAt Z t→ℕ}{φ':Q.TypeAt Z t→ℕ}
    (U_:Plans U' b φ') (he:C.ref 0 < b) (hG:G.Simple)(hD:∀ i,i∉p₀→ C.ref (d i) ≤ b!)(hp:∀ k,d k≠0→k∉p₀→φ' k=b!) : ∃ P₁:∀ m,Q.TypeAt Z t→Cup (C.path.rep N p m), Ledger Θ b! s' (grouped_X F Φ) P₁ (motif Z Q u t) φ' z'! y! D∧
    (∀ k∈p₀,∀ i,P₁ i k=F' i ((Φ).twig k))∧ ∀ k∉p₀,Minted C N p b! (d k) (Ω*z'! b! k) (s'! b! k) (P₁ b! k):=by
    obtain ⟨p₁,hp₁,hΩ,hΨ⟩:= arrivesForm (U:=U) L h U' A J' he hG d hD; let v':= z'!; let X' k:=Ω* v' b! k; let w₁:= Finset.univ.filter (fun i:(Q.TypeAt Z t)=> i∉p₀ ∧ d i=0); have he' k:k∈w₁ ↔ k∉p₀∧d k=0:=by simp [w₁]
    let t':= afterGoal φ b! Φ p₀; have hz(k)(hi:k∉p₀): t' k=b!:=if_neg hi
    have hx:Cash x:=⟨A.rate.1,A.rate.2⟩; have ht:0 < T:= (lt_of_lt_of_le (b:=Fintype.card I) (Fintype.card_pos_iff.mpr ⟨Q.star⟩) ((Nat.le_add_right ..).trans U'.enough)); have hT:= Q.belowLaunch S U'.tall; have hX:= Tariff.amounts L hG ht hx hT; obtain ⟨-,-,hy,-,-,hα⟩:=Tariff.checkOut L hG ht hx hT
    have hr(k: Q.TypeAt Z t)(hk:k∈ w₁): Minted C N p b! 0 (X' k) (s'! b! k) (p₁ b! k)∧ lifted z'! y! b! k*(4*stampOut C b! 0 (X' k)) ≤ fly (Y) 0 b!:=by
       obtain ⟨hp,hq⟩:= (he' k).1 hk; exact ⟨hq ▸ hΨ k hp,Tariff.spaWidth hX.1 hy.have_ hα (hp₁.clock.ready ..)⟩
    have h_f(k)(h:k∉w₁): φ' k=t' k:=by
       by_cases hx:k∉p₀
       · change φ' k=t' k; rw [hp k (fun ht=>h ((he' k).2 ⟨hx,ht⟩)) hx,hz k hx]
       exact (U_.terms k (not_not.mp hx)).trans (if_pos (not_not.mp hx)).symm
    obtain ⟨Q',hh₁,hQ,hE⟩:= Ledger.rolling L h hp₁ X' w₁ hG he.le (fun k h=>let p:=(he' k|>.1 h).1; ⟨U_.fund k,le_trans (U_.max k p) (hz k p).ge⟩) h_f (fun k h=>hz _ (he' k|>.1 h).1) (fun k h=> U_.located _ (he' k|>.1 h).1) hr
    exact ⟨Q',hh₁,(fun k hk i=> (hE k (show k∉ w₁ from (fun hi=> (he' k|>.1 hi).1 hk)) i).trans (hΩ k hk i)), fun k he=> hQ.symm ▸ hΨ k he⟩
end Store
end Rhythm
end YM.OPE.Log.Trunk
