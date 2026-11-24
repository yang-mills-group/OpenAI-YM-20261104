import YM.RegulatorIR.Momentum.Renew

/-! W1 cutoff difference at a real Path step. No actual coupling data
in this use. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Layer Budget.Tuple Lattice Laurent Geometry Spatial Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior Work.F08 RegulatorIR.Quadratic
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {G:Gauge}{v p:ℕ}{σ τ τ' σ' A A' F F' J S δ ε δ' ε':ℝ}
section small
variable {X Y W V: Type}
-- artillery lemma. all lap edges with Billed. avoids block orientation to distance when comparing graft
lemma counts_profile {M:Layer X Y}{P:Layer Y W}(h:Billed M)(hv:Billed P) x z: Summable (fun y=>M x y * P y z) :=by
 obtain ⟨c,hc,hv⟩:=hv; apply quota_summable (w:=1) (fun _=>le_rfl)
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows _) hc); rw [quota_base,quota_base,← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro i; rw [enorm_mul]; apply mul_le_mul_right; refine le_trans ?_ (hv i); have he:= term_le (P i) 1 z; simpa using he
lemma lapL {M P:Layer X Y}{H:Layer Y W}(h:Billed M) (hp:Billed P)(hv:Billed H) : lap (M-P) H=lap M H - lap P H :=by ext1 x;ext1 y;unfold lap; simp only [Pi.sub_apply,sub_mul]; exact (counts_profile h hv x y).tsum_sub (counts_profile hp hv x y)
lemma lapR {M: Layer X Y}{F P: Layer Y W}(h:Billed M)(hp:Billed P)(hv:Billed F): lap M (F-P)=lap M F - lap M P:= by ext1 x;ext1 y; unfold lap;simp only [Pi.sub_apply,mul_sub]; exact (counts_profile h hv x y).tsum_sub (counts_profile h hp x y)
lemma lap_tools {M:Layer X Y}{H:Layer Y W}{P: Layer W V} (h:Billed M)(hp:Billed H)(hv:Billed P):lap M (lap H P)=lap (lap M H) P:=by
 ext1 i;ext1 j;unfold lap
 simp_rw [← tsum_mul_right,← tsum_mul_left,mul_assoc]; refine Summable.tsum_comm (f:=fun (w:W) (y:Y)=>_) (?_)
 obtain ⟨c,hc,hx⟩:=hp; obtain ⟨b,hb,hU⟩:=hv; apply quota_summable (w:=1) (fun _=>le_rfl)
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows _) (ENNReal.mul_ne_top hc hb));rw [quota_base,quota_base, ← ENNReal.tsum_mul_right, ENNReal.tsum_prod', ENNReal.tsum_comm]; apply ENNReal.tsum_le_tsum; intro y
 simp only [Function.uncurry_apply_pair, enorm_mul];rw [ENNReal.tsum_mul_left]; apply mul_le_mul_right; apply le_trans _ (mul_le_mul_left (hx y) b); rw [quota_base,← ENNReal.tsum_mul_right];apply ENNReal.tsum_le_tsum;intro a; apply mul_le_mul_right; have he:= term_le (P a) 1 j; simp only [Pi.one_apply,mul_one] at he; exact he.trans (hU a)
lemma billing_point {M:Layer X Y} (h:Billed M):∃ c≠⊤,∀ x y, ‖M x y‖ₑ≤c:=by
 obtain ⟨c,hc,hv⟩:=h; refine ⟨c,hc,fun x y=>?_⟩; apply le_trans _ (hv x); simpa using term_le (M x) 1 y
-- Hank kernel noncentered. express via Quiver. no Ward or Momentum yet.
lemma lamp_gain {U L: Layer (Long X) (Long Y)}{T:Layer (Long X) (Long X)} (V:Billed L)(H:Billed (Function.swap U))(h:Billed T): lamp (lap (Function.swap U) (lap T L))=unfoldQ ![U,L] (lamp T) :=by
 ext1 x
 let a:= x 0; let b:=x 1; let g (i j:Long X):= U i a *(T i j*L j b)
 let f (v: Tuple (Long X) 2) := T (v 0) (v 1) * ∏ i, (![U,L]:Fin 2→ Layer _ _) i (v i) (x i)
 let p:Long X × Long X≃ Tuple (Long X) 2:= ((Equiv.prodCongr (Equiv.refl _) (Pert.Bulk.identify _).symm).trans (glueEquiv (Long X) 1))
 have hz : Summable fun z:Long X × Long X=> g z.1 z.2:=by
    obtain ⟨c,hc,hv⟩:= billing_point V; obtain ⟨B,hB,W₀⟩:= h
    apply quota_summable (w:=1) (fun _=>le_rfl); apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (H.rows a) (ENNReal.mul_ne_top hB hc)); rw [quota_base,quota_base, ← ENNReal.tsum_mul_right, ENNReal.tsum_prod']; apply ENNReal.tsum_le_tsum;intro i; unfold g; simp_rw [enorm_mul]; rw [ENNReal.tsum_mul_left]; apply mul_le_mul_right; apply le_trans _ (mul_le_mul_left (W₀ i) c); rw [quota_base,← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun j=> mul_le_mul_right (hv j b) _
 change (∑' i,U i a*(∑' j,T i j*L j b))=∑' t,f t
 rw [← p.tsum_eq f,tsum_congr (g:=fun t:Long X × Long X=>g t.1 t.2) (fun t=>?_)]
 · simp_rw [← tsum_mul_left]
   exact hz.tsum_prod.symm
 unfold f g; rw [Fin.prod_univ_succ,Fin.prod_univ_succ, Fin.prod_univ_zero]; change T _ _ * (U t.1 a*(L t.2 b*1))=_; change T t.1 t.2 *(U t.1 a*(L t.2 b*1))=_;ring
end small

variable (G:Gauge) (K:KernelChoices)(P:Patch)
variable {B C D E:Precision.Bed}
variable (R R' : Cross P.L (TypeFace 1) (TypeFace 1))
variable {s l t q:RG.Clip}
variable (H:Hall B σ F δ s)(Ω: Hall C τ A ε l)(Z: Hall D σ' F' δ' t)(H': Hall E τ' A' ε' q)
variable (S₁: BidP P K B C R σ J)(S₂:BidP P K D E R' σ' S)
local notation "e"=> projectionQ P K R G
local notation "e'"=>projectionQ P K R' G
local notation "A0"=> ruling P G R
local notation "A1"=> ruling P G R'
local notation "P₀"=> crust G B
local notation "P₁"=> crust G C
local notation "P'"=> crust G D
local notation "P''"=>crust G E

include H Z S₁ S₂ H' Ω
lemma penny : lamp (P₁-P'')=unfoldQ ![A0,A1] (lamp (P₀-P')):=by
 have hp:= (overrides P K R G S₁.rows H.pos.le S₁.costV).buys H.pos.le
 have hv: Billed e':= (overrides P K R' G S₂.rows Z.pos.le S₂.costV).buys Z.pos.le|>.1
 have ha: Billed A0∧ Billed (Function.swap A0):= (fond (blockQ G P.L) (linksQ G) _ (adult_price G P R S₁.rows S₁.costV)).buys H.pos.le
 have hV:Billed A1:= ((fond (blockQ G P.L) _ _ (adult_price G P R' S₂.rows S₂.costV)).buys Z.pos.le).1
 have h:=crust_f G B H.stripP.2.1 H.pos.le H.paid
 have d:=crust_f G D Z.stripP.2.1 Z.pos.le Z.paid
 have ht: Function.swap (P₀-P')=P₀-P':=congr_arg₂ (·-·) (symmetry_h G B H.floorP H.pos.le H.paid H.stripP.2.1) (symmetry_h G D Z.floorP Z.pos.le Z.paid Z.stripP.2.1)
 rw [upwards G K P R R' H Ω Z H' S₁ S₂,lapL h d hv,comm_lane G K P B H R' S₂.rows S₂.costV Z.pos.le,comm_lane G K P D Z R' S₂.rows S₂.costV Z.pos.le,← lapL h d hV,lap_tools hp.2 (h.sub d) hV, ← lamp_gain hV ha.2 (h.sub d), lap_tools ha.2 (h.sub d) hV]
 have he:lap (P₀-P') e=lap (P₀-P') A0:=by rw [lapL h d hp.1,lapL h d ha.1,comm_lane G K P B H R S₁.rows S₁.costV H.pos.le,comm_lane G K P D Z R S₁.rows S₁.costV H.pos.le]
 have ht' : lap (Function.swap e) (P₀-P')=lap (Function.swap A0) (P₀-P'):=by
    have hf:=congr_arg Function.swap he; rw [lap_flip,lap_flip,ht] at hf;exact hf
 rw [ht']
lemma km_paid (p:ℕ)(v:ℝ≥0∞)(hx:v≠⊤)(hd:3≤p)(HP: PriceW A0 P.L.val p 3 v)(HT:PriceW A1 P.L.val p 3 v) (C':ℝ≥0∞) (hC:C'≠⊤) (hc:Held (lamp (P₀-P')) p C'):
 Held (lamp (P₁-P'')) p (fore_c G.ColorIndex 1 p 3 v * award P.L.val * C'):=by
 rw [penny G K P R R' H Ω Z H' S₁ S₂]
 have h:∀ i:Fin 2, PriceW (![A0,A1] i) P.L.val p 3 v:=fun i=>by fin_cases i;exact HP; exact HT
 have he:= obtains_h (L:=P.L) (r:=1) h hc hd (neighboring H Z G) (self_r G R) 1 (by decide) hx hC -- check order
 simpa only [pow_one,mul_zero,add_zero] using he
end YM.RegulatorIR.Momentum
