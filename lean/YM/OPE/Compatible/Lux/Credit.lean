import YM.OPE.Compatible.Lux.SumSpectrum
/-!
# Readout costs on full geometry. No sibling separation in projections assumed. Lateral arbitrary (with fixed clearance).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Table MeasureTheory Cov Display Survey Trace
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
   {I J V:Type}[Fintype J][Fintype I][PartialOrder I][OrderBot I]
variable (D:Origin I){Q:Finset I}(A:Allot C)(hL:Lanes (F:=F) U.sector.derivatives)(hs:Services C F S)
variable {ψ:Filter V}{T: V→ℝ}{s:V→I→ℝ}{η M c:ℝ} {x:V→I→E4}(H: Burst D Q ψ T s)
local notation "o" => fun i=> x i ⊥
-- uncentered positions
variable (hx:∀ᶠ i in ψ,Ridge (s i) η M D Q (away (x i) (x i ⊥)))(hη:0<η)(hM:0 ≤ M)
variable (t:brim D Q →ℕ) (p:brim D Q→ S.Tag)(y: V→J→ E4)(q:J→ S.Tag)(v:V→Viewers U)
variable (P:Prescription U.sector.derivatives)(hP:P.Coherent)
local notation "k"=> brim D Q
set_option quotPrecheck false
local notation "Y" => fun i=> picked (brim D Q) (x i)
local notation "Y'"=> fun i=> away (Y i) (o i)
local notation "B!"=>fun i=>s i ⊥
-- using explicit d

def costed (D:Origin I)(Q:Finset I)(d:ℕ)(p:brim D Q→ℕ)(s:I→ℝ):ℝ:= volume D Q p s / s ⊥^d
local notation "Z"=> fun d i=> costed D Q d (Sigma.fst∘p) (s i)
include H
lemma cost_pos (d:ℕ): ∀ᶠ i in ψ,0 < Z d i:=by
   let g:= Ward.expose ∘ p; have ht:=H.fresh 1 one_pos; filter_upwards [ht.brim_paid D g,(ht.fade _ ht.crowned.base).eventually self_mem_nhdsWithin] with i hi hp; exact div_pos hi (pow_pos hp _)
include hx hη
lemma finish_view {W:Finset I} (g:W ⊆ Q)(p:Crown W):
    Tendsto (fun i=> away (picked (brim D W) (x i)) (o i)) ψ (𝓝 0) ∧ ∀ᶠ i in ψ, Injective (picked (brim D W) (x i)):= by
    have ht:= H.fresh _ hη; have he(i:brim D W):i.val∈ allUp D Q:=brim_under D Q W g i.2
    constructor
    · apply tendsto_pi_nhds.mpr; intro a; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (g:=fun i=> M*s i ⊥) ?_
      filter_upwards [hx] with i hi; have hv:=hi.near _ _ ht.crowned.base (he a) bot_le; rw [hi.belly,zero_sub,norm_neg] at hv; exact hv
      simpa using ((ht.fade _ (ht.crowned.base)).mono_right nhdsWithin_le_nhds|>.const_mul M)
    filter_upwards [hx,(time_bright D ht).lit] with i hi hh a b hab; by_contra h
    have hp: (a:I) ≠ b:= Subtype.val_injective.ne h; have hv := brim_apart D W p a.2 b.2 hp; have hg:= lt_of_lt_of_le (mul_pos hη (hh.pos _ (diverge D ht.crowned (he a) hv))) (hi.span _ _ (he a) (he b) hv (brim_apart D W p b.2 a.2 hp.symm)); unfold away at hg; change x i a=x i b at hab; rw [hab,sub_self,norm_zero] at hg; exact lt_irrefl _ hg
lemma clear_awayU (hc:∀ᶠ i in ψ, ClearOf (o i) (y i) c)(h:0<c): -- order far
     (∀ᶠ i in ψ, ClearOf 0 (away (y i) (o i)) c)∧ ∀ᶠ i in ψ,Injective (beside (picked (brim D Q) (x i)) (y i))∧ Injective (beside (sole (o i)) (y i)):=by
   have hY:∀ᶠ i in ψ, ClearOf 0 (away (y i) (o i)) c:=hc.mono (fun i hh=>by
       constructor
       · intro j; unfold away; rw [zero_sub,norm_neg,norm_sub_rev]; exact hh.openSpace j
       intro a b he; unfold away; rw [sub_sub_sub_cancel_right]; exact hh.spread a b he)
   have ht:= clear_shifted D (fun i=>away (y i) (o i)) H (M:=M) (row_root D H) h hY hη _ (Finset.mem_union_left _ (Burst.crown D H|>.base)); refine ⟨hY,?_⟩; filter_upwards [ht,hx,hY] with i hi hx he; have hf:= hi _ hx; rw [hx.belly,show away (away (x i) (o i) ∘ Subtype.val) (0:E4)=away (Y i) (o i) from funext fun j=>sub_zero _] at hf; constructor
   · rw [beside_away] at hf -- orientation
     exact (away_inject ..).mp hf
   have h_: Injective (beside (sole (0:E4)) (away (y i) (o i))):= he.inject_both h; have hQ:away (sole (o i)) (o i)=sole 0:=funext fun _=>sub_self _; rw [← hQ,beside_away] at h_; exact (away_inject ..).mp h_
include A hL hs hM hP
lemma earns (w:Mode U.sector.derivatives): PaidWeight ψ T (Z w.fst) (fun i=> P.ope w (Y i) (Ward.expose∘p) (o i)):=by
   let t':=Ward.expose ∘ p; obtain ⟨f,hf,he⟩:= sturdy_coeff D U A hs hL hP t' H hη hM w
   unfold PaidWeight; apply Score.pointwise hf; swap; · exact ((cost_pos D H p w.fst).mono fun i h=> mul_nonneg h.le (norm_nonneg _)) -- arg order
   filter_upwards [he,hx] with i he hi; have hh:=he _ hi; let A:=P.ope w (Y i) t' (o i)
   have hw : P.ope w (picked (brim D Q) (away (x i) (o i))) t' 0=A:=(show P.ope w (Y' i) t' 0=A from (sub_self (o i)) ▸ ope_away P t' (Y i) (o i) (o i) w)
   rw [hw] at hh; refine le_trans (le_of_eq ?_) hh; change (_ /_) * ‖A‖= _; change _= ‖A‖* volume D Q (Sigma.fst∘p) (s i)/_; ring
lemma era_shadow (d:ℕ)(hc:∀ᶠ i in ψ,ClearOf (o i) (y i) c)(h:0<c): PaidWeight ψ T (Z (d+1)) (fun i=> kernel (spectator U (v i)) (beside (Y i) (y i)) (beside p q) - Cov.insert S (spectator U (v i)) (o i) (y i) q d (shadow P d (Y i) (Ward.expose ∘ p) (o i))) :=by
   obtain ⟨hY,he⟩:=clear_awayU D H hx hη y hc h; let t':= Ward.expose ∘ p; let w:= Ward.expose ∘ q; obtain ⟨f,hf,hQ⟩:= sturdy_test D U A hs hL hP t' v (fun i=>away (y i) (o i)) w H hη hM d h hY
   unfold PaidWeight; apply Score.pointwise hf; swap; · exact ((cost_pos D H p (d+1)).mono fun i h=> mul_nonneg h.le (norm_nonneg _))
   filter_upwards [he,hx,hQ] with i he hi hm
   let V:= spectator U (v i); let A:= observe V (beside (Y i) (y i)) (beside t' w); let B:=P.truncated V d (Y i) t' (o i) (y i) w
   have hl:=hm _ hi; have hz:= spectate U (v i)
   have hu: observe V (beside (picked _ (away (x i) (o i))) (away (y i) (o i))) (beside t' w)=A:= by change observe V (beside (Y' i) (away (y i) (o i))) _=_; dsimp only; rw [beside_away]; exact observe_away V (beside t' w) _ (o i) hz.translations he.1 -- defeq beside_away no
   have hF:P.truncated V d (picked _ (away (x i) (o i))) t' 0 (away (y i) (o i)) w=B:= (sub_self (o i)) ▸ trunc_away P _ _ _ _ _ _ _ _ hz he.2
   rw [hu,hF] at hl; rw [kernel_expose,beside_commutes,Cov.insert,compatible_shadows P _ hz (spectate_respects U _) (spectate_ready U _) _ he.2]; apply le_trans (le_of_eq ?_) hl; change (_/_) * ‖A-B‖= _; change _= ‖A-B‖* volume D Q (Sigma.fst∘p) _ /_; ring
end YM.OPE.Arboreal
