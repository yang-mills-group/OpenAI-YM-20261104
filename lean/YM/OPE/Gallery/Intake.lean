import YM.OPE.Gallery.Clock
/-! # Intervals between and within grouping events.

Use less than exponent supplies. Bits & Sleeper states compatible across steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Drapery
open scoped Topology BigOperators Classical
variable {I J V L B X : Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side}
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype L][DecidableEq L]
    [Fintype B][DecidableEq B][Fintype X][DecidableEq X]
set_option quotPrecheck false
namespace Lecture
variable {H:History G}{N p i k m j q b r' T:ℕ} {A:Fibers I J}{K:Fibers I L}{C:Fibers L J}
    {δ ψ φ α η : ℕ→ℝ} {r z:ℕ→ℕ} {x y:ℝ}
    {D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
    {t:∀ m:ℕ, I→ Site (H.S.side m p)}{X₀:I→ Config G (H.S.side N p)→ℂ}
    {W:ℕ→ I→ℝ}
    {P:Playout H p b N V}
local notation "Ξ"=> H.rep N p
structure BudgetStop (H:History G)(D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)) (δ ψ φ:ℕ→ℝ)(z:ℕ→ℕ)(η:ℕ→ℝ)(r:ℕ→ℕ)(b:ℕ):Prop where
    counts: Monotone r
    amounts a: b ≤ a → 8 ≤ z a ∧ z a ≤ (H.levels.budget a).B ∧ 1 ≤ δ a*η a*mintK (z a)
    params a:b ≤ a→ 0<η a ∧ η a≤1 ∧ 0<δ a∧δ a≤1
    host: Thor H δ r D ψ φ b
    well: H.Selected

/-- Utility replicate denominator in occupancy monotone (capacities per current step supply). -/
lemma occupied_trans {a:I→ Site (H.S.side i p)} {k:ℕ}(h:P.occupied k a)(L:Fibers I J) : P.occupied k (a ∘ L.twig):=by
    let f:= P.spectrum i a; intro y; let p:=univ.filter (fun i=>(f ∘ (partialGroup V L).twig) i=y); have he : p.image (partialGroup V L).twig ⊆ univ.filter fun i=> f i=y:=by
       intro i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
    exact (le_of_eq (card_image_of_injective p (partialGroup V L|>.sectioned.injective)).symm).trans ((card_le_card he).trans (h y))

/- Geometry, separation mask compared in phase. Endpoints included (both). Group stops need weaker.
-/
variable {s: Ward (Names V I)}
def Spaced (s:Ward (Names V I)) (f:V×I→Site n) (M:ℕ) := ∀ i j, room s i j → i ≠ j → M ≤ separation (f i) (f j)
-- Peg uses source spends through birth.Monitor
lemma moderated {q} (B0:BudgetStop H D δ ψ φ z η r q){a:I→ Site (H.S.side i p)}{W W':I→ℝ}
    (hp:q ≤ i)(hw:∀ k,0<W' k)(hF:∀ k,η i*W' k ≤ W k)
    (h:Spaced s (P.spectrum i a) ((H.levels.budget i).B*z i)) : s.Cares (P.spectrum i a) (H.levels.budget i).B (fun u:V×I=> δ i*W u.2) (W' ∘ Prod.snd) (1/2):=by
    have hr:= B0.amounts i hp; obtain ⟨hη,hL,hδ,-⟩:= B0.params i hp; let W₀:= fun u:V×I=>δ i*W u.2; let W₁ (u:V×I):=W' u.2; have hu:= hr.2.2; let d:= (H.levels.budget i).B
    have he(v:V×I): W₁ v ≤ W₀ v *mintK (z i):=by let t:=mintK (z i); have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hF v.2) hδ.le) (show 0 ≤ t from (Real.exp_pos _).le); exact (le_mul_of_one_le_left (hw _|>.le) hu).trans ((le_of_eq (b:=δ i*(η i*W' v.2)* t) (by unfold t; ring)).trans h')
    intro u hu hv t ht; have hm := OPE.Log.separatedMarks u.val (P.spectrum i a) (fun i hi j hj=> h i j ⟨u,hu,hi,hj⟩) hr.1 (Nat.one_le_iff_ne_zero.mpr (H.levels.budget i|>.B_pos).ne') hv t ht
    unfold Poly.toll; refine (prod_le_prod (fun i _=> hw i.2|>.le) (fun i _=>he i)).trans ?_
    rw [prod_mul_distrib,prod_const]; refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun j _=> mul_nonneg hδ.le ((mul_pos hη (hw j.2)).trans_le (hF j.2)|>.le))
    unfold mintK;rw [← Real.exp_nat_mul]; have hp:(z i:ℝ)*u.val.card ≤64*(coverNumber (H.levels.budget i).B t:ℝ):=by exact_mod_cast hm
    apply Real.exp_monotone; linarith only [hp]
-- No growth throughout long intervals
variable (h : BudgetStop H D δ ψ φ z η r q)
include h
lemma intervalMarket (hL:Trial s)(hk:k ≤ j) (hr:q ≤ k)(hp:b ≤ k)(hn:j ≤ N)
    {F:∀ i:ℕ,I→ Cup (H.rep N p i)}
    (hw:∀ m,k ≤ m→ m ≤ j→ ∀ i,0<W m i)
    (hy:∀ m,k ≤ m→ m < j → ∀ i,t m i=(H.levels.clock.op m p).ratio.parent (t (m+1) i) ∧ η m*W m i ≤ W (m+1) i)
    (hω:∀ m,k ≤ m→m < j → P.occupied (r m) (t m) ∧ P.occupied (r m) (t (m+1))∧ Spaced s (P.spectrum m (t m)) ((H.levels.budget m).B * z m))
    (hΦ:P.Market s (t j) (F j) (P.intention X₀ j hn) (W j) ((H.levels.budget j).supportExponent-3))
    (hE:∀ i,Continuous (X₀ i)) (hB:∀ i, Program H N p k j (fun j=>t j i) (fun j=> F j i) (fun m=> W m i) D hn) : ∀ i,k ≤ i→∀ hJ:i ≤ j, P.Market s (t i) (F i) (P.intention X₀ i (hJ.trans hn)) (W i) ((H.levels.budget i).supportExponent-3):=by
    intro i hk hi; induction hi using Nat.decreasingInduction with
    | self=>exact hΦ
    | of_succ i hi IH=>
       choose x hx using fun j=>(hB j).follows i hk hi; let V:= P.intention X₀ i (hi.le.trans hn); obtain ⟨he,hq,hW⟩:= hω i hk hi; have hG:= IH (hk.trans i.le_succ); have hl:=hi.trans_le hn; have ht:=hr.trans hk; have ha:=hp.trans hk; have hw':= hw i hk hi.le
       rw [P.intention_step X₀ hl]; exact (Playout.Market.strides P h.well h.host ht ha hl hG (by linarith only) (P.paidFor X₀ h.well hE hl) (fun j=> (hy i hk hi j).1) hq he hx |>.peek P h.well h.host ha ht hl he hL hw' (moderated h ht hw' (fun j=> (hy i hk hi j).2) hW)).shy P hw' le_rfl (by linarith only)
end Lecture
end YM.MergeProof.Ribbons.ManyCopies.Cadet
