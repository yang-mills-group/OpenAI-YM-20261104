import YM.OPE.Loom.Span
/-!
# Program on the root (actual flow) new narrow-halo estimate
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker YM.Next.Rank.Station YM.Extra.Multi YM.Next.Rank Cells Menu
variable {G:Gauge} {C:Family G}{n:Side}{k p m j N t :ℕ}{v : ℝ} {α: Type}[Fintype α][DecidableEq α] (a:α→Site (C.side j p))
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "P" => C.path.levels.budget
local notation "S" => C.S
local notation "V" => Site (C.side m p)
set_option quotPrecheck false
local notation "F" i => radiusCost C t i
local notation "L" i => stride C 50 i
variable {W r D} (A : Sharper C W r D) (hk:m ≤ k) (hg:k+1 < j)
-- stripe measured in physical units with 4 vs 1. shape min gap etc.
structure Gate (C:Family G)(r:ℕ→ℕ)(t k j m:ℕ)(v:ℝ) : Prop where
   pos : 0<v
   width : v ≤ threshold C 50 (k+1)
   mind (i) : k+1 < i → i ≤ j → threshold C 50 i<v
   fine : broad C 50 j < v
   tr (i) : k+1 ≤ i → r i ≥ Fintype.card α
   light (i) : k+1 ≤ i → Loom.stride C 50 i-4 ≤ (C.path.levels.budget i).B^2
   sail p : ∀ hm:m≤k+1,(C.path.levels.budget (k+1)).B^2+1+2*(t*Loom.stride C 50 (k+1)+1) ≤ (C.S.toDepth hm p).count.val
-- notation L i problematic
variable (H : Gate (α:=α) C r t k j m v) (he:∀ i,‖C.S.place (a i)‖ ≤ v*t) (hE:∀ i j:α,i≠j→ 4*v ≤ ‖C.S.place (a i-a j)‖)
local notation "f" => (fun (i:ℕ) (t:V×α)=> bites C m j p (a t.snd) i (t.fst,true))
local notation "T'" => Mix.camp C p m
local notation "c" => (fun (i:α)=> loops C j p (a i) (k+1))
include hg he H
omit [DecidableEq α] in
lemma closer (i:α): separation (c i) 0 ≤ t*stride C 50 (k+1)+1:=by
   apply upper (a i) hg.le
   refine le_trans ((he i).trans (mul_le_mul_of_nonneg_right H.width (Nat.cast_nonneg _))) (le_of_eq ?_); unfold threshold; push_cast; ring
include hk A
lemma highCross (i:ℕ) (hi:k+1 ≤ i)(hj:i≤j): Cross (P i).B (f i):=by
    have hw:Brine C.path (k+1) δ η:=⟨fun i _=> A.system.costs.stay.water _ (Nat.zero_le i),fun i _=> A.system.costs.stay.mint _ (Nat.zero_le i),fun i _=> A.system.costs.stay.split _ (Nat.zero_le i),fun i _=> A.system.costs.stay.support _ (Nat.zero_le i)⟩
    apply innerCross C k p m m a le_rfl hk (fun u z h=>?_) hw i hi hj
    exact across (hk.trans k.le_succ) _ _ (closer a hg H he u.2) (closer a hg H he z.2) (H.sail p _) _ _ h
include hE
lemma wider (i:ℕ)(hi:k+1 < i)(hj:i≤j)(x y: V×α)(hxy:x≠y):stride C 50 i-4 ≤ separation (f i x) (f i y):=by
    obtain ⟨x,l⟩:=x; obtain ⟨y,z⟩:=y; by_cases hy:x=y; swap; · exact (H.light i hi.le).trans (highCross a A hk hg H he i hi.le hj (x,l) (y,z) hy)
    subst y; unfold bites; simp only [affine,ite_true, separation_signed,separation_translate]
    apply Loom.lower hj; refine le_trans ?_ (hE _ _ (fun H=>hxy (H ▸ rfl)))
    let D:= stride C 50 i; let X':ℝ:= C.S.a i; have hp:= C.S.a_pos i; have hx : 4≤D:=by unfold D stride;omega
    have ht:(D:ℝ)*X' < v := H.mind i hi hj; have hl: ((D-4:ℕ):ℝ)+1 ≤ D:= by rw [Nat.cast_sub hx, Nat.cast_ofNat]; linarith only
    change 2*X'*(((D-4:ℕ):ℝ)+1)≤_
    nlinarith only [ht,mul_le_mul_of_nonneg_left hl hp.le,H.pos]
lemma spacious : Edition.Spaced (P j).B (f j):= (highCross a A hk hg H he j hg.le le_rfl).together (fun u _ t=> bit C m j p j (a t) (by omega) u true) (by
   intro i l hil; simp_rw [biteT C m j p j _ (by omega), Ribbons.same]; let B:= (P j).B
   have h := normC C j p (a i-a l)
   have h' := H.fine; have ht := h.2; rw [← separation_alt] at ht
   have ha:= C.S.a_pos j; have hh : v > C.S.a j*((B:ℝ)^2+1):= lt_of_le_of_lt (mul_le_mul_of_nonneg_right (gate_b (C:=C) 50 j) (by positivity)) h'
   have hv : (B:ℝ)^2 ≤ separation (a i) (a l):= by nlinarith only [ha,H.pos,hE i l hil,ht,hh]
   exact_mod_cast hv)
omit hk H he hE hg
lemma secret : ∃ χ:ℕ→ℝ,∀ d:ℕ,SwornClusterCuts C (μ:=D) («δ»:=δ) (r:=r) (C.ref d) d χ δ (fun i=>X (i+1)):=by
   obtain ⟨c0,hc⟩:= A.productCuts.mother
   exact ⟨c0,fun d=> { hc d with dollars _ _ := ((Y).fits.delayed _).le, brings i he N p hi := ⟨((hc d).brings i he N p hi).1,A.improves i _ _ _ he hi⟩ }⟩
include hk he hE hg H
local notation "n" => Fintype.card α
variable (w:α→ℝ) (s : α→ℕ) (u : ∀ i,C.label (s i))
local notation "u'"=> fun i:α=> δ j*(η j*w i)/8
local notation "w'"=> fun i:ℕ=> fun l:α=> priced C (k+1) j ((u') l) i
omit hk A he hE hg H in
def purse (C : Family G) (w:α→ℝ) (j k t:ℕ) := cashIn C.path (renal C.path.levels) (Fintype.card α) (radiusCost C t (k+1)) (k+1)
    (fun l:α=> priced C (k+1) j (renal C.path.levels j*(near C.path.levels j*w l)/8) (k+1))
local notation "K'" => purse C w j k t
lemma gate_consumer (hK:C.Makes) (d K:ℕ)(ht:0<t)(hZ:C.ref d ≤ K)(hb:K ≤ k)(hm: Stock.Tabs.opens C.path.levels 1 m K)(hu:∀ i,C.ref (s i) ≤ j)(hp':∀ i,w i*Spindle.paid C (s i) j N p (u i) ≤ ζ (s i) j)(hw:∀ i,0<w i)(hN:j<N)(hq:GridApprox.room C.path.levels m k (lensScope C d))(i:α)(hA:a i=0)
   (Y₀:α→ Config G (C.side N p)→ℂ)(hy:∀ i,Y₀ i=C.O N p (u i) ((C.S.toDepth hN.le p).embed (a i)))
   (hi': m ≤ N) (hR:∀ i, Interior ((center C.S p hi' 0).chamber 0) (Y₀ i)) (hC:∀ z:C.label d, Interior ((center C.S p hi' 0).chamber 0) (C.O N p z 0)):
    ∃ z:C.label d, Next.UVStress.quota C d k N p z ≤ 2*ebb C d k K' ∧
      let g:Config G (C.side N p)→ℂ := (fun u=>∏ i,Y₀ i u)-C.O N p z 0
      Interior ((center C.S p hi' 0).chamber 0) g ∧ (center C.S p hi' 0).rootTest (C.beta N p) g ≤ 2*(stakes C m K / bid C d K k K'):=by
    have hq'(j x):0 < renal C.path.levels j* (near C.path.levels j*w x)/8:= by have he:= A.system.costs.stay.water j (Nat.zero_le j); exact div_pos (mul_pos he.2 (mul_pos he.1 (hw _))) (by norm_num)
    have hw₀(x : α):0<u' x:=hq' j x; have hf(u : α)(j'): 0 < w' j' u:=price_pos (hw₀ _)
    let B:= (P (k+1)).B; have hB:B>0:= (P (k+1)).B_pos
    let q:= t*(count C 50 (k+1)+10); have ht':q>0:= by unfold q; positivity
    have hk0:B*(q-1) ≥ t*stride C 50 (k+1)+1:=by
       -- t=1: B*(p+9) vs B(p+2)+5
       unfold B q stride at *; generalize (P (k+1)).B=d₁ at * -- b reducible?
       generalize count C 50 (k+1)=c' at *
       have h': 1 ≤ t*(c'+10):= ht'; rw [show d₁*(t*(c'+10)-1)= d₁*(t*(c'+10))-d₁ by rw [Nat.mul_sub_left_distrib, mul_one]]
       have hh:=Nat.le_mul_of_pos_left t hB; have hv:=Nat.le_mul_of_pos_right d₁ ht; have he:t*(d₁*(c'+2)+4)=t*d₁*(c'+2)+4*t:=by ring
       rw [he, show d₁*(t*(c'+10))= t*d₁*(c'+2)+8*(d₁*t) by ring]; omega
    obtain ⟨z,hχ⟩:= secret A
    have hp: 0 < purse C w j k t:= cashIn_pos _ _ ((hχ d).funs (k+1) (hZ.trans (hb.trans k.le_succ))).1 (Fintype.card_pos_iff.mpr ⟨i⟩) (fun i=> hf i _)
    obtain ⟨hqB,hPP,h₃⟩ := prices A d K hZ hp hb
    apply enlarged_joins C N k p d m K i _ w a hm.1 hb hN hg.le s u hK A.system A.literal (hχ d) A.tabs hm hZ hu hp' hw hq (fun u0=>by rw [hA]; exact at_point _) w' (funext fun l=>price_top hg) (fun i _ _ l=>hf l i) (fun i hi h=> bucket (P i|>.B_pos) (H.tr _ hi) (highCross a A hk hg H he i hi h.le)) (spacious a A hk hg H he hE) _ (fun j hi hh l=> price_march hi (hw₀ _)) hg (radiusCost C t (k+1)) _ Y₀ hy hR hC hp (le_refl _) hqB hPP (le_refl _) h₃
    · intro i' hi hj; rcases eq_or_lt_of_le hi with heq|hr
      · subst i'; exact erase (fun x=>hf x.snd _) (fun x=> price_last (hw₀ _))
      exact peg_nonempty (fun l=> hf l.2 _) (fun l=> hf l.2 _) (fun l=>price_next hi (hw₀ _)) (fun s _ x _ y _=>wider a A hk hg H he hE i' hr hj.le x y)
    intro z'; let f' := T' (k+1) z'.1; have hl : bites C m j p (a i) (k+1) (z'.1,true) = f':= hA ▸ at_point _
    have hsep:separation (bites C m j p (a z'.2) (k+1) (z'.1,true)) f' ≤ t*stride C 50 (k+1)+1:= (reachBit C m j p (k+1) (a z'.2) (hk.trans k.le_succ) _ true).trans (closer a hg H he _)
    dsimp only; rw [hl]; exact (Loom.assembled _ _ ((separation_comm ..).trans_le (hsep.trans hk0))).trans_eq (Nat.sub_add_cancel ht')
end YM.OPE.Loom
