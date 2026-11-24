import YM.GradedFar.Bill
import YM.GradedFar.ForkReducedImports
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
/-!
# Physical G4 two-scale prices (part of G6 payment). In terms of tree tokens.

Continued adaptation from WilsonPublicForkStage/Ordinary; now uniform centers & viewers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log Node
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] {P:Prescription F.sector.derivatives}
local notation "spots" => Fork.position
local notation "nearSet" => Fork.near I J
local notation "outerSet" => Fork.outer I J
local notation "tree'" => Fork.tree I J
local notation "T" => Node I J

def bare {α:Type}:Fin 0 → α:=Fin.elim0
abbrev vacant : Fin 0 → E4 := bare

private theorem restored {b n c u:ℝ}(hb:0<b)(h:u ≤ c*(n/b)) : b*u ≤ c*n:= by
  calc _ ≤ b*(c*(n/b)):=mul_le_mul_of_nonneg_left h hb.le
       _=_:=by field_simp

theorem inner (bank:LogTrace F P)(p:T → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠr:ℝ in 𝓝[>]0,∀(t:ℝ)(o:E4)(x:I→E4)(z:J→E4),Setting M δ x z →
      r^(load p)*‖coalesce P nearSet (spots o r t x z) p child w‖  ≤  badge r^k*r^w.1:=by
  obtain ⟨k,h⟩:=bank.terms ↥nearSet (crop p nearSet) δ M dp mn w
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r issued pos
  intro t o x z hx
  have bill:=(issued (crop (spots o r t x z) nearSet) o (leafRoom o pos hx.xhome hx.xclear)).2
  rw [innerdeg] at bill; exact restored (pow_pos pos _) bill

theorem outside (bank:LogTrace F P)(p:T → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(z:J→E4), Setting M δ x z → ∀v:Viewers F,
      t^(w.1+premium p)*‖flux P (spectator F v) outerSet
          (spots o r t x z) (update p child (P.letter w)) base vacant bare 0‖ ≤ badge t^k*t:=by
  let b:=outerSet
  let u:=update p child (P.letter w)
  obtain ⟨k,h⟩:=bank.horizons ↥b (Fin 0) (crop u b) bare δ M 1 dp mn zero_lt_one 0
  refine ⟨k,?_⟩; filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r o x z hz v
  have he:ClearOf o vacant 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:= (issued (crop (spots o r t x z) b) vacant o
    (outerRoom o pos mn dp.le hz.zhome hz.away hz.zclear) he).2.2.phaseBound v
  change _ ≤ badge t^k*(t^(0+1)/t^sigma (crop (update p child (P.letter w)) outerSet)) at bill
  rw [outerdeg,pow_one] at bill; exact restored (pow_pos pos _) bill

theorem full (bank:LogTrace F P)(p:T → C.book.Token){M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(z:J→E4),0<r → r ≤ t → Setting M δ x z → r*M ≤ t*δ → ∀v:Viewers F,
      mass p r t*‖flux P (spectator F v) (tree').leaves
        (spots o r t x z) p base vacant bare 0‖ ≤ t*(badge t*badge r)^k:=by
  obtain ⟨k,h⟩:=bank.testing tree' p (bare:Fin 0 → C.book.Token) 0 M δ 1 mn dp zero_lt_one
  refine ⟨k,?_⟩; filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r o x z hr rt hx room v
  let sites':=spots o r t x z; let rad:T→ℝ:=radius r t
  have convoy:=actual o hr rt mn dp.le hx room
  have he:ClearOf (sites' (tree').root) vacant 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:=(issued sites' rad vacant rfl convoy he k le_rfl).ready.phaseBound v
  have wager:=convoy.sizes.fee_pos (b:=(tree').leaves) p 1 (tree').initial
  have eq:=convoy.sizes.reward_eq 1 p
  have cost:=mul_le_mul_of_nonneg_left bill wager.le
  change (tree').fee p rad (tree').leaves (tree').root 1*
      ‖flux P (spectator F v) (tree').leaves sites' p base vacant bare 0‖ ≤ _ at cost
  rw [Arboreal.listPrice,←mul_assoc,mul_comm ((tree').fee ..) ((tree').tariff ..),eq,one_mul] at cost
  change _ ≤ (Arboreal.prestige tree' (radius r t))^k at cost; rw [Fork.prestige] at cost
  change (tree').fee p (radius r t) (tree').leaves (tree').root 1*_ ≤ _ at cost
  rw [Fork.fee,pow_one] at cost
  have paid:=mul_le_mul_of_nonneg_left cost pos.le
  rwa [←mul_assoc,mul_div_cancel₀ (mass p r t) pos.ne'] at paid

set_option maxHeartbeats 800000 in
theorem joint (bank:LogTrace F P)(p:T→C.book.Token)(h:ℕ)(a:Mode F.sector.derivatives)
    (zero:a.1=0){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(z:J→E4),0<r → r≤t → Setting M δ x z → r*M≤t*δ →
      mass p r t*‖coalesce P (tree').leaves (spots o r t x z) p base a-
        ∑b∈bands F.sector.derivatives h,coalesce P nearSet (spots o r t x z) p child b*
          coalesce P outerSet (spots o r t x z) (update p child (P.letter b)) base a‖
        ≤ (badge t*badge r)^k*(r/t)^(h+1):=by
  obtain ⟨k,hk⟩:=GradedFar.WilsonThermometerWeakNestedChild.original F bank tree' p a (fun _=>h)
    child Fork.middle M δ mn dp
  refine ⟨k,hk.mono ?_⟩
  intro t available r o x z hr rt hx room
  have rate:=available (spots o r t x z) (radius r t) rfl (actual o hr rt mn dp.le hx room)
  rw [Fork.fee,zero,pow_zero,div_one,Fork.prestige,Fork.ratio,incoming, Fork.pruned] at rate
  change _≤(badge t*badge r)^k*(r/t)^(h+1) at rate; convert rate using 1
  congr 3; apply Finset.sum_congr rfl; intro b _; apply congrArg₂ (·*·) rfl
  apply congrArg (fun pp=>coalesce P outerSet (spots o r t x z) pp base a)
  funext j; by_cases hj:j=child
  · subst j;simp [Function.update]
  · simp [Function.update,hj]

-- horizon-zero terms on actual S at any viewer
variable (P)
def ZeroReading (a : Mode F.sector.derivatives) (v : Viewers F) (o:E4) :=
  observe (spectator F v) (beside (sole o) vacant) (beside (sole (P.letter a)) bare)
lemma zero_common (hG : G.Simple) (a : Mode F.sector.derivatives) (ha : a∈ bands F.sector.derivatives 0) :
    ∀ o v, ZeroReading F P a v o = ZeroReading F P a none 0 := by
  obtain hh : a.fst = 0 := Nat.eq_zero_of_le_zero ((full_bands ..).mp ha)
  have hT := F.phase.transport.comparator
  obtain ⟨_,U⟩ := hT
  obtain ⟨X,_⟩ := U a.1
  have eq : Module.finrank ℂ (S.Field a.1)=1 := X.finrank_eq.trans
    (UVNext.FreeStress.dim_before C.book.grid hG (hh.trans_lt zero_lt_four))
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' (S.unit _) (S.alive _ F.room.kernel.laws)).1
    eq (P.needle a)
  suffices ∀ o v, ZeroReading F P a v o = c from fun o v=> by rw [this,this]
  intro o v; have Hb := spectate F v; have Hc := spectate_respects F v
  have Hx : Injective (beside (sole o) vacant) := beside_distinct.mpr
    ⟨injective_of_subsingleton _, injective_of_subsingleton _, fun _ j => Fin.elim0 j⟩
  unfold ZeroReading Prescription.letter; rw [← projectedOne (spectator F v) _ _ _ Hb.laws.toSymmetric Hc Hx,S.rep,
    ← hc,map_smul]; change _ • observeOne S _ _ _ _ _ (S.project _ _) = _
  rw [projectedOne _ _ _ _ Hb.laws.toSymmetric Hc Hx]
  change c • observe _ _ (beside (sole (C.book.one a.1)) (bare:Fin 0→C.book.Token)) = _
  rw [local_one_mem _ _ _ _ Hb.laws Hx,
    OPE.card_zero_eq _ Hb.laws, smul_eq_mul,mul_one]

lemma flowed (hG : G.Simple) (v:Viewers F) (p:T→C.book.Token) (x:T→E4)(s:Finset T) :
    flux P (spectator F v) s x p base vacant bare 0 = whole (spectator F v) s x p vacant bare -
    ∑w∈bands F.sector.derivatives 0, coalesce P s x p base w*ZeroReading F P w none 0 := by
  rw [flow_eq]; congr 1; exact Finset.sum_congr rfl fun w hw=> congrArg (_*·) (zero_common F P hG w hw _ v)

theorem phase (hG : G.Simple) (bank:LogTrace F P)(p:T → C.book.Token){M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(z:J→E4),0<r → r ≤ t → Setting M δ x z → r*M ≤ t*δ → ∀v:Viewers F,
      mass p r t*‖whole (spectator F v) (tree').leaves (spots o r t x z) p vacant bare -
        whole (spectator F none) (tree').leaves (spots o r t x z) p vacant bare‖ ≤ 2*(badge t*badge r)^k*t := by
  obtain ⟨k,h⟩:= full F bank p mn dp; refine ⟨k,h.mono ?_⟩
  intro t ht r o x z hr hrt hx hg v; let E : Viewers F → ℂ := fun v=>flux P (spectator F v) (tree').leaves
    (spots o r t x z) p base vacant bare 0
  have H : E v - E none = whole (spectator F v) (tree').leaves (spots o r t x z) p vacant bare -
      whole (spectator F none) (tree').leaves (spots o r t x z) p vacant bare := by
    simp_rw [E,flowed F P hG]; ring
  have hM:0 ≤ mass p r t:=mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrt) _)
  rw [← H]; refine (mul_le_mul_of_nonneg_left (norm_sub_le ..) hM).trans ?_
  rw [mul_add]; specialize ht r o x z hr hrt hx hg; exact
    (add_le_add (ht v) (ht none)).trans_eq (by ring)

theorem sum_shadow (hG : G.Simple) (bank:LogTrace F P)(p:T→C.book.Token)(h:ℕ){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(z:J→E4),
      0<r → r≤t → Setting M δ x z → r*M≤t*δ → ∀v:Viewers F,
        let X:=spots o r t x z
        mass p r t*‖whole (spectator F v) (tree').leaves X p vacant bare -
          ∑u∈bands F.sector.derivatives h,coalesce P nearSet X p child u*
            whole (spectator F v) outerSet X (update p child (P.letter u)) vacant bare‖ ≤
        b*(badge t*badge r)^K*(t+(r/t)^(h+1)):=by
  let A:=↥(bands F.sector.derivatives 0); let B:=↥(bands F.sector.derivatives h)
  let pay a:= ZeroReading F P a none 0
  choose ih earns using fun u:B=>Fork.inner F bank p u.1 mn dp
  choose oh owes using fun u:B=>Fork.outside F bank p u.1 mn dp
  choose ah heard using fun a:A=>Fork.joint F bank p h a.1 (Nat.eq_zero_of_le_zero ((full_bands ..).mp a.2)) mn dp
  obtain ⟨k,allpay⟩:=Fork.full F bank p mn dp
  obtain ⟨r₀,pos,inside⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp (Filter.eventually_all.mpr earns)
  let K:=k+(∑i,ih i)+(∑i,oh i)+(∑j,ah j)
  let b:ℝ:=1+(∑a∈bands F.sector.derivatives 0,‖pay a‖)+(bands F.sector.derivatives h).card
  refine ⟨b,K,by dsimp [b];positivity,?_⟩
  have late : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ min 1 r₀ :=
    (ge_mem_nhds (lt_min zero_lt_one pos)).filter_mono nhdsWithin_le_nhds
  filter_upwards [late,allpay,Filter.eventually_all.mpr owes,Filter.eventually_all.mpr heard] with t h₀ hf ho ha
  intro r o x z hr rt hx room v; dsimp only
  have ht:=hr.trans_le rt
  have nearRates:=inside (show r∈Ioc (0:ℝ) r₀ from ⟨hr,rt.trans (le_min_iff.mp h₀).2⟩)
  have t1:1≤badge t:=by unfold badge run;linarith [Real.log_nonpos ht.le (le_min_iff.mp h₀).1]
  have r1:1≤badge r:=by unfold badge run;linarith [Real.log_nonpos hr.le (rt.trans (le_min_iff.mp h₀).1)]
  let L:=badge t*badge r; have L1:1≤L:=one_le_mul_of_one_le_of_one_le t1 r1
  have eqpos:0 ≤ mass p r t:=by dsimp [mass]; positivity
  let X:=spots o r t x z; let c (u:Mode F.sector.derivatives):=coalesce P nearSet X p child u
  let pp (u:Mode F.sector.derivatives):=update p child (P.letter u)
  let q (u a:Mode F.sector.derivatives):=coalesce P outerSet X (pp u) base a
  let upper (a:Mode F.sector.derivatives):=coalesce P (tree').leaves X p base a
  apply GradedFar.WilsonThermometerWeakPairBudget.original (bands F.sector.derivatives h)
    (bands F.sector.derivatives 0) (whole (spectator F v) (tree').leaves X p vacant bare)
    (fun u=>whole (spectator F v) outerSet X (pp u) vacant bare) c upper pay q eqpos
    (pow_nonneg (zero_le_one.trans L1) K) (pow_nonneg (div_nonneg hr.le ht.le) _) ht.le
  · have bill := hf r o x z hr rt hx room v; rw [flowed F P hG] at bill
    refine bill.trans ?_
    rw [mul_comm t]; exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ L1 (show k≤K by dsimp [K];omega)) ht.le
  · intro a ha'; let e:A:=⟨a,ha'⟩
    have hK:ah e≤K:=by
      have paid:ah e≤∑u,ah u:=single_le_sum (fun u _=>Nat.zero_le (ah u)) (mem_univ e); dsimp [K];omega
    exact (ha e r o x z hr rt hx room).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ L1 hK) (pow_nonneg (div_nonneg hr.le ht.le) _))
  · intro u hu; let e:B:=⟨u,hu⟩
    have ihK:ih e≤K:=by
      have paid:ih e≤∑u,ih u:=single_le_sum (fun u _=>Nat.zero_le (ih u)) (mem_univ e); dsimp [K];omega
    have ohK:oh e≤K:=by
      have paid:oh e≤∑u,oh u:=single_le_sum (fun u _=>Nat.zero_le (oh u)) (mem_univ e); dsimp [K];omega
    have now:=nearRates e t o x z hx
    have next:=ho e r o x z hx v; rw [flowed F P hG] at next
    have row:=GradedFar.WilsonThermometerWeakPairResidual.product hr rt (norm_nonneg _)
      (pow_nonneg (zero_le_one.trans r1) _) (pow_nonneg (zero_le_one.trans t1) _) now next
    apply row.trans; apply mul_le_mul_of_nonneg_right _ ht.le
    rw [mul_pow,mul_comm]; exact mul_le_mul (pow_le_pow_right₀ t1 ohK) (pow_le_pow_right₀ r1 ihK)
      (pow_nonneg (zero_le_one.trans r1) _) (pow_nonneg (zero_le_one.trans t1) _)
end YM.Integration.GradedFar.Fork
