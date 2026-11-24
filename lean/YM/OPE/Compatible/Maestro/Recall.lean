import YM.OPE.Compatible.Maestro.Temper
/-!
# Exponential filter versus budget filter. hereditary receipts for the ruler
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{I : Type}{l:Filter I}{T r : I→ℝ}{q:I→ℕ}{i n b:ℕ}
open YM.OPE
lemma grows_scale (C:Family G)(_:G.Simple) : ∀ᶠ i in (atTop:Filter ℕ), β C i ≤ ((C.S.scale i)^2):=by
   let t:=G.slopeConstant; let a:= C.path.levels.clock.bar
   filter_upwards [C.S.divergent.eventually_ge_atTop a,C.S.divergent.eventually_ge_atTop (t+1),C.S.divergent.eventually_ge_atTop 0] with i hi hp hx; change a+t*C.S.scale i ≤ _; nlinarith only [hi,hp,hx]
-- actually didn't need slope
lemma scale_coin (hG:G.Simple)(h:Tendsto q l atTop)(ht:Tendsto T l atTop)(hs:Score l T (fun i=>C.S.scale (q i))):Round l T (fun i=>β C (q i)):=
   Round.if_inv (Eventually.of_forall fun _=> β_pos ..) ((hs.power 2 ht).pointwise (h.eventually (grows_scale C hG)) (Eventually.of_forall fun _=>(β_pos ..).le)) ht (Eventually.of_forall fun _=>(β_one ..).le)
-- successive β bounded by same Score (including forward overshoot)
lemma stepβ (A:Allot C)(hG:G.Simple){q:I→ℕ} (hp:Tendsto T l atTop)(h:Score l T (fun i=>β C (q i))) : Round l T (fun i=> β C (q i+1)):=by
   refine Round.if_inv (Eventually.of_forall fun _=>β_pos ..) ?_ hp (Eventually.of_forall fun _=>(β_one ..).le)
   refine (h.plus ((Score.steady G.slopeConstant hp).product h) hp).pointwise ?_ (Eventually.of_forall fun _=>(β_pos ..).le)
   filter_upwards with i; let a:=q i; let c:= β C a
   have he: Real.log (extent C a) ≤ c:= le_trans (Real.log_le_self (le_trans (by norm_num) (extent_two ..))) (block_cheap A _)
   have hz : β C (a+1)=c+G.slopeConstant*Real.log (extent C a) := by unfold β c; simp_rw [β,Calendar.hatBeta]; rw [Schedule.scale_succ,mul_add,add_assoc]
   exact hz.trans_le (add_le_add_right (mul_le_mul_of_nonneg_left he (G.slopeConstant_pos hG|>.le)) _)
lemma tick_score (hp:Tendsto T l atTop)(h:Score l T (fun i=>β C (q i))) : Score l T (fun i=> ((bins C (q i)).B:ℝ)):=by
   refine Score.ceiling (Score.power (p:=fun i=> Real.log (β C (q i))) 2 (h.pointwise (Eventually.of_forall fun i=> Real.log_le_self (x:=β C (q i)) (β_pos ..|>.le)) (Eventually.of_forall fun _=> Real.log_nonneg (β_one ..|>.le))) hp) hp (Eventually.of_forall fun i=> sq_nonneg _) -- inspect
lemma gap_score (hp:Tendsto T l atTop)(h:Score l T (fun i=>β C (q i+1))) (d:ℕ): Score l T (fun i=> (gapL C d (q i):ℝ)):=by
   have hV :0 ≤ (64:ℝ)*((d:ℝ)+2):=by positivity
   let x i:=β C (q i+1); have hv(i):0 ≤Real.log (x i):= Real.log_nonneg ((β_one ..).le); refine Score.ceiling ((Score.steady _ hp).product (h.pointwise (Eventually.of_forall (fun i=> Real.log_le_self (x:=x i) (β_pos ..|>.le))) (Eventually.of_forall hv))) hp (Eventually.of_forall (fun i=> mul_nonneg hV (hv i))) -- inspect
lemma valve_price (A:Allot C)(hG:G.Simple)(hq:Tendsto q l atTop)(ht:Tendsto T l atTop)(h:Score l T (fun i=>β C (q i))) {H L d:ℕ}(hp:0<H) {m:I→ℕ}(he:∀ᶠ i in l,m i ≤ L*(1+gapL C d (q i))) : Round l T (fun i=> Lights.valve C H b (m i) (q i)):=by
    have hf:= stepβ A hG ht h; let u i:=β C (q i+1)
    have hj : ∀ᶠ i in l,0 < Lights.valve C H b (m i) (q i):=(hq.eventually_ge_atTop (C.ref 0)|>.mono fun i hi=> Lights.valve_pos C A _ _ hp hi)
    let f i:=(100+1/2:ℝ)*(m i); have hY(i):0≤f i:=by unfold f; positivity
    have hz: Round l T (fun i=> Real.exp (f i)):=by
       obtain ⟨a,hA⟩:= hf.up.fitsQ ht
       let w:ℝ:=100+1/2; let t:ℝ:=64*((d:ℝ)+2); have hw:0≤ w:=by norm_num [w]
       have hL:0 ≤ w* (L:ℝ):=by positivity
       let g i:= gapL C d (q i); have hg(i):0 ≤ t*Real.log (u i):=mul_nonneg (by unfold t; positivity) (Real.log_nonneg (β_one ..|>.le))
       refine Round.if_inv (Eventually.of_forall (fun i=>Real.exp_pos _)) ?_ ht (Eventually.of_forall fun _=>Real.one_le_exp (hY _))
       let x i:=Real.log (T i); let A':=w*(L:ℝ)*(2+t*a)
       have hw := (RateLE.exp A' (Real.tendsto_log_atTop.comp ht)); refine Score.pointwise ⟨A',hw⟩ ?_ (Eventually.of_forall (fun i=>Real.exp_nonneg _)); filter_upwards [he,hA,(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,ht.eventually_gt_atTop 0] with i hi hx hB hp
       have hx_: Real.log (u i) ≤ (a:ℝ)*x i:= (Real.log_le_log (β_pos C _) ((Real.le_norm_self _).trans hx)).trans_eq (Real.log_pow ..)
       refine Real.exp_monotone ?_
       have he: (m i:ℝ) ≤ (L:ℝ)*(1+g i):= by exact_mod_cast hi
       have hk: (g i:ℝ) < t*Real.log (u i)+1:=Nat.ceil_lt_add_one (hg i)
       change w* ↑(m i) ≤ A'*x i; unfold A'; rw [mul_assoc]; change 1 ≤ x i at hB
       have hw0 : 0 ≤ w:=by norm_num [w]
       have ht0 :0 ≤ t:=by unfold t; positivity
       have hf : 1+(g i:ℝ) ≤ (2+t*↑a)*x i:=by nlinarith only [hk,hB,mul_le_mul_of_nonneg_left hx_ ht0]
       rw [←mul_assoc]; calc
          _ ≤ _ := mul_le_mul_of_nonneg_left he hw0
          _ = w* ↑L * (1+g i) := (mul_assoc ..).symm
          _ ≤ w* ↑L*((2+t*↑a)*x i):= mul_le_mul_of_nonneg_left hf hL
          _= _ :=by ring
    let v i:=renal C.path.levels (q i); have he:Round l T v:= (hf.power 2 ht).inv.adjust (Eventually.of_forall fun i=> (renal_eq ..).symm)
    apply ((Round.const one_pos ht).less (((((he.div (Round.const (by exact_mod_cast hp : (0:ℝ) < H) ht)).mul he).div hz).div (hf.power b ht))) ht).adjust
    filter_upwards with i; simp only [Lights.valve,license, A.fixed]; rfl
end YM.OPE.Allot
