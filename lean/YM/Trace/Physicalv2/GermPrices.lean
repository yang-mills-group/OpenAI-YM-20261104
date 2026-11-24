import YM.Trace.Physicalv2.GermStep
import YM.Pert.Spatial.Prices
/-! Prepaid-tail comparison prices on the same construction carrying
`Materials.room`; these are *without* reserving the fresh analytic model
replacement errors. Rates here are in threshold coordinates. -/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof Motion
open YM.MergeProof.Ribbons
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 125000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 3600
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
variable {G:Gauge}(C:Family G)
local notation "P" => C.path.levels
local notation "σ" => (fun i:ℕ=>(C.path.levels.params i).supportExponent)
local notation "s" => C.S.scale
local notation "b'" => (P).clock.hatBeta
local notation "L" => factor C
local notation "F" => C.labels.level
abbrev rate :ℝ:= (1:ℝ)/8
lemma pCover (i:ℕ): 4*(↑((plank C i).B):ℝ)+2 ≤ 10*(b' i)^2 := by
    let b:= b' i; have hb :1 < b:= (P).fits.delayed i
    have hx:0 ≤ Real.log b := Real.log_nonneg hb.le
    have hp : ((plank C i).B : ℝ) ≤ (Real.log b)^2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
    change _ ≤ 10*b^2
    have he :0 ≤ b:= zero_le_one.trans hb.le; have h':= pow_le_pow_left₀ hx (Real.log_le_self he) 2
    nlinarith
lemma cut_flat (h:G.Simple)(δ:ℝ): ∀ᶠ i in atTop, ∀ p:ℕ, cut (C:=C) p i ≤ Real.exp (δ*s i) := by
    have hb: Note C.S (b') 0 := Ribbons.hut C h
    let σ₀:= σ 0
    have hσ :0<σ₀:= (stage C 0).price_pos
    let fee:=100*(4+σ₀⁻¹)
    have hf:=((Note.notes C.S fee (by unfold fee; positivity)).mills (hb.powerN 2)).mills (Note.bell_exp C.S (1/2))
    have hv:=hf.outweigh (Note.bell_exp C.S 1) (by norm_num)
    let B(i):=Real.exp ((1/2:ℝ)*s i)
    have ht := isLittleO_pow_exp_pos_mul_atTop 1 (one_pos (α:=ℝ))
    let w(i):=1/2*s i
    have hS:Tendsto (w) atTop atTop:=(P).clock.schedule.divergent.const_mul_atTop (by norm_num:0<(1/2:ℝ))
    let c:ℝ:=2*|δ|+1
    have he:Tendsto (fun i=> w i / B i) atTop (𝓝 0):=by simpa only [comp_def,pow_one,one_mul] using! ht.tendsto_div_nhds_zero.comp hS
    have hw : ∀ᶠ i in atTop, (-δ)*s i ≤ B i:=by
        have hpos:0<c:= by unfold c; positivity
        filter_upwards [he.eventually (gt_mem_nhds (inv_pos.mpr hpos)), (P).clock.schedule.divergent.eventually_ge_atTop 0] with i hi hs₀
        change w i/B i < c⁻¹ at hi
        have hn := hi.le; have hE :0<B i:=Real.exp_pos _
        field_simp [ne_of_gt hpos,hE.ne'] at hn
        have hz := hs₀;change 0 ≤ s i at hz
        unfold w c at hn
        have hA := mul_le_mul_of_nonneg_right (neg_le_abs δ) hz
        -- needs 2 factor?
        nlinarith
    filter_upwards [hv,Ribbons.hut C h |>.pos |> Filter.Eventually.of_forall, (P).clock.schedule.divergent.eventually_ge_atTop 0,hw] with i hi _ h₁₀ hE p
    have hn:= C.S.a_pos i
    change 0 ≤ s i at h₁₀
    change cut (C:=C) p i ≤ _
    let n:= C.side i p
    have hn0 : Real.exp (s i) ≤ n.val:= by
       unfold Schedule.scale;rw [Real.exp_log (inv_pos.mpr hn)]; unfold Schedule.a;rw [inv_inv];exact mod_cast (Nat.le_mul_of_pos_left _ (C.S.period p).property)
    rw [show cut p i = _ from (rfl : cut (C:=C) p i =Real.exp (2*σ i - σ i * n.val / (10*(4*((plank C i).B:ℝ)+2))))]
    apply Real.exp_le_exp.mpr
    change fee*(b' i)^2*B i ≤ Real.exp (1*s i) at hi
    rw [one_mul] at hi; replace hi:=hi.trans hn0
    have hσ':σ₀≤σ i:= (P).fits.deepExp (Nat.zero_le _)
    have h0:(1:ℝ) ≤ B i:= Real.one_le_exp (by linarith)
    have h1: 4 + B i/σ₀ ≤ (4+σ₀⁻¹)*B i:=by field_simp; nlinarith
    have h2 : (4+B i/σ₀)*(10*(4*((plank C i).B:ℝ)+2)) ≤ n.val := le_trans (mul_le_mul h1 (mul_le_mul_of_nonneg_left (pCover C i) (by norm_num: (0:ℝ)≤10)) (by positivity) (by positivity)) (by unfold fee at hi; linarith)
    replace h2 := (le_div_iff₀ (by positivity)).mpr h2
    have h3 := mul_le_mul_of_nonneg_left h2 (hσ.trans_le hσ').le
    rw [mul_div_assoc]; have hp:= h0; have h4:σ i*(B i/σ₀) ≥ B i:=le_trans (by rw [show σ₀*(B i/σ₀)=B i by field_simp]) (mul_le_mul_of_nonneg_right hσ' (div_nonneg (zero_le_one.trans hp) hσ.le))
    change 2*σ i - σ i * ((↑n.val:ℝ) / (10*(4*↑(plank C i).B+2))) ≤ _
    linarith only [h3,h4,hσ',hσ,hE]
private lemma price_pos (d:ℕ):0 < price (C:=C) d := mul_pos (by exact_mod_cast (Nat.zero_lt_succ _)) (germ_close (F d) C.params|>.choose_spec.1)
lemma open_late (h:G.Simple)(d:ℕ) : ∀ᶠ i in atTop, ∀ p, Opened C d i p := by
    have hp:=(Note.notes C.S (2*8*price (C:=C) d) (by have:=price_pos C d; positivity)).mills (Ribbons.fuNote C)
    have hx := hp.mills (Note.bell_exp C.S (-1))
    filter_upwards [hx.outweigh (Note.notes C.S 1 zero_lt_one) (by norm_num), cut_flat C h (-1), eventually_ge_atTop (C.ref d)] with i hi ht hh p
    refine ⟨hh,?_⟩
    unfold invoice; have hz:0 ≤ price (C:=C) d:=price_pos C d|>.le
    change _ * stock C i * _ ≤ 1 at hi
    calc
       _ ≤ price (C:=C) d * Real.exp (-1*s i) * stock C i := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht p) hz) (zero_le_one.trans (stage C i|>.columns_ge))
       _ < 1/4 := by linarith only [hi]

lemma factor_cost (i:ℕ):
    Real.log (2:ℝ) + Real.log (stock C (i+1)) ≤ 2 * ((↑((P).clock.J (i+1)):ℝ)^2)⁻¹*Real.log (factor C i):= by
    have hL:1<L i:=by exact_mod_cast (lt_of_lt_of_le (by norm_num:(1:ℕ)<3) (C.S.block_large i))
    have hp := (P).fits.logCost i
    let t:=stage C (i+1)
    have h₁:2 ≤ 1+t.paths+t.width⁻¹+t.columns+t.clip.relaxation+t.supportExponent:= by
       have hσ := (stage C (i+1)).price_pos
       have hc:=t.clip.radius_pos
       linarith [t.paths_pos,(inv_pos.mpr t.width_pos),t.columns_ge,hc]
    have h₂:=Real.log_pos hL; let j:ℝ:=((P).clock.J (i+1):ℝ)
    replace hp := (div_le_iff₀ h₂).mp hp
    have h₃ := Real.log_le_log (by norm_num:(0:ℝ)<2) h₁
    have h₄ := Real.log_le_log (zero_lt_one.trans_le t.columns_ge) (show t.columns ≤ 1+t.paths+t.width⁻¹+t.columns+t.clip.relaxation+t.supportExponent by linarith [t.paths_pos,(inv_pos.mpr t.width_pos),h₁,t.price_pos,t.clip.radius_pos])
    change _ ≤ _*(j^2)⁻¹*_; change Real.log _ ≤ (j^2)⁻¹ * Real.log (factor C i) at hp
    have hE : Real.log 2 ≤ (j^2)⁻¹ * Real.log (factor C i) := le_trans h₃ hp
    have h' : Real.log (stock C (i+1)) ≤ (j^2)⁻¹ * Real.log (factor C i) := le_trans h₄ hp
    linarith
lemma factor_large (γ:ℝ)(hγ:0<γ): ∀ᶠ i in atTop, γ⁻¹ ≤ factor C i ∧ 4*stock C (i+1) ≤ (factor C i)^γ := by
    let j i:ℝ:=((P).clock.J (i+1):ℝ)
    have hj : Tendsto (fun i=> (j i^2)⁻¹) atTop (𝓝 0) := (tendsto_pow_atTop (show (2:ℕ)≠0 from by decide)|>.comp (tendsto_natCast_atTop_atTop.comp ((P).fits.deep.comp (tendsto_add_atTop_nat 1)))).inv_tendsto_atTop
    filter_upwards [hj.eventually (gt_mem_nhds (show 0<γ/4 by linarith)),hj.eventually (gt_mem_nhds (show 0<Real.log (2:ℝ)/(4/γ) by refine div_pos (Real.log_pos one_lt_two) ?_; positivity))] with i hi hx
    have h0 :0≤(j i ^2)⁻¹:=by positivity
    change (j i^2)⁻¹ < _ at hi hx
    have hn := (factor_cost C i)
    have hH :1< factor C i:=by exact_mod_cast (lt_of_lt_of_le (by norm_num:(1:ℕ)<3) (C.S.block_large i))
    have hLog:0<Real.log (factor C i):=Real.log_pos hH
    have hS :0 ≤ Real.log (stock C (i+1)):=Real.log_nonneg (stage C (i+1)|>.columns_ge)
    have hK : γ⁻¹ ≤ Real.log (factor C i) := by
       by_contra! h'
       field_simp at hx
       have ha:=mul_le_mul_of_nonneg_left h'.le (mul_nonneg zero_le_two h0)
       change _ +_ ≤ 2 * (j i ^2)⁻¹ * _ at hn
       rw [div_eq_mul_inv] at hx
       have h0' := mul_lt_mul_of_pos_left hx (show 0<γ⁻¹ from inv_pos.mpr hγ)
       have hK' : γ⁻¹*(Real.log (2:ℝ)*γ) = Real.log (2:ℝ):=by field_simp
       nlinarith [Real.log_pos (one_lt_two)]
    refine ⟨hK.trans (Real.log_le_self (zero_le_one.trans hH.le)),?_⟩
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hH)]; refine (Real.exp_log (mul_pos (by norm_num) (zero_lt_one.trans_le (stage C _).columns_ge))).symm.le.trans (Real.exp_le_exp.mpr ?_)
    rw [Real.log_mul (by norm_num: (4:ℝ)≠0) (zero_lt_one.trans_le (stage C _).columns_ge).ne', show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num: (2:ℝ)≠0) (by norm_num: (2:ℝ)≠0)]
    change _ +_ ≤ 2 * (j i ^2)⁻¹ * _ at hn
    nlinarith

lemma contract_rate {d m p} (hp:Opened C d m p)(h : Opened C d (m+1) p)(hL:(16:ℝ) ≤ factor C m){η:ℝ}(he:η≥0)(ht:(1+2*(stock C m))*η ≤ barunit (C.S.block m)) : stableLoss C d p m η ≤ (factor C m)^(-rate):=by
   let x:= factor C m
   have h0:=show 0<x from (by linarith)
   let u:= x^rate
   have hu : 0<u:=Real.rpow_pos_of_pos h0 _
   have he₈ : u^8 = x:=by rw [show u^8=x^(rate*(8:ℝ)) from by rw [Real.rpow_mul h0.le,show (8:ℝ)=(8:ℕ) by norm_num,Real.rpow_natCast], show rate*(8:ℝ)=1 by unfold rate;norm_num,Real.rpow_one]
   have h₄ : (2:ℝ) ≤ u^2:= by
      by_contra! hh; have hz:= pow_le_pow_left₀ (by positivity) hh.le 4
      have hs₁:=mul_lt_mul hh (le_refl _) (by positivity:0<u^2) (by norm_num)
      nlinarith [sq_nonneg (u^2)]
   have hm₀ :0 ≤ stock C m :=zero_le_one.trans (stage C m).columns_ge
   have hm₁ :0 ≤ stock C (m+1) := zero_le_one.trans (stage C (m+1)).columns_ge
   have hE : 0 ≤ 1 + startLoss C d p m :=by unfold startLoss; have hY:= invoice_nn (C:=C) d p (m+1); exact add_nonneg zero_le_one (mul_nonneg hm₁ hY)
   have hX : η*(1+startLoss C d p m) ≤ η*(5/4):=mul_le_mul_of_nonneg_left (by unfold startLoss; have := h.small; linarith) he
   have hq : coordLoss C d p m η ≤ (5/4)*(η*(5/4)):=by unfold coordLoss; rw [mul_assoc]; exact mul_le_mul (by linarith [smaller d p hp]) hX (mul_nonneg he hE) (by norm_num)
   have hS :stableLoss C d p m η ≤ 2*(1+2*stock C m)*η:=by unfold stableLoss; nlinarith
   have hq := mul_le_mul_of_nonneg_left ht zero_le_two
   have h2 : 2*barunit (C.S.block m) ≤ (factor C m)^(-rate):=by
      rw [Real.rpow_neg h0.le]; change 2*u⁻¹ ^3 ≤ u⁻¹
      calc
         _ ≤ u^2 * u⁻¹ ^3 := mul_le_mul_of_nonneg_right h₄ (by positivity)
         _ = u⁻¹ := by field_simp
   exact le_trans (by linarith only [hq,hS]) h2

private lemma read_nonneg {d N i p:ℕ}{r:ℝ}{q : Coefficient (F d) (C.side i p)}(h : reads d N p i q r) : 0 ≤ r:= by obtain ⟨a,b,ha,hb,h0,-⟩:=h.2;linarith
private lemma read_weaken {d N i p:ℕ}{r u:ℝ}{q : Coefficient (F d) (C.side i p)}(h : reads d N p i q r)(hu:r≤u) : reads d N p i q u := by obtain ⟨a,b,ha,hb,h0,h'⟩:=h.2; exact ⟨h.1,a,b,ha,hb,h0.trans hu,h'⟩
private lemma factor_note : Note C.S (factor C) 0:=⟨fun i=>Nat.cast_pos.mpr (C.S.block i).property,show Tendsto (fun i=>_) atTop (𝓝 (0:ℝ)) from (P).fits.mesh⟩
private lemma feed_tail (h:G.Simple)(d:ℕ)(ε:ℝ)(he:0<ε): ∀ᶠ i in atTop, ∀ p:ℕ, (factor C i)^rate *(2*(stock C (i+1))*(factor C i)^d * invoice (C:=C) d (i+1) p) ≤ ε/2 := by
    have h0 := Ribbons.fuNote C |>.scales (P).fits.mesh
    have hp:=(factor_note C|>.powerN d).swapP (show (d:ℝ)*0=(0:ℝ) from mul_zero _)
    have hq:= (factor_note C|>.powr rate).swapP (mul_zero rate)
    have hf:= hq.mills (((Note.notes C.S 2 two_pos).mills h0 |>.mills hp).mills ((Note.notes C.S (price (C:=C) d) (price_pos C d)).mills (Note.bell_exp C.S (-1*1)|>.scales (P).fits.mesh)))
    have hi := hf.outweigh (Note.notes C.S (ε/2) (half_pos he)) (by norm_num)
    filter_upwards [hi, (tendsto_add_atTop_nat 1).eventually (cut_flat C h (-1*1))] with i hi hq p
    unfold invoice
    apply le_trans ?_ hi
    have ht:0≤factor C i:=by unfold factor;positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hq p) (price_pos C d|>.le)) (mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans (stage C _|>.columns_ge))) (pow_nonneg ht _))) (Real.rpow_nonneg ht _)
private lemma factor_top : Tendsto (factor C) atTop atTop:= tendsto_atTop.2 (fun a=> by
    let b:=max 1 a
    have hb:0<b:=zero_lt_one.trans_le (le_max_left ..)
    filter_upwards [factor_large C b⁻¹ (inv_pos.mpr hb)] with i hi; exact le_trans (le_max_right ..) (inv_inv b ▸ hi.1))
private lemma coord_tail (d:ℕ)(ε:ℝ)(he:0<ε): ∀ᶠ i:ℕ in atTop, ∀ p, Opened C d i p → Opened C d (i+1) p → ∀ η,0≤η → (1+2*stock C i)*η ≤ barunit (C.S.block i) →
      factor C i ^ rate * coordLoss C d p i η ≤ ε/2:=by
    let z i := (factor C i)^rate
    have hz:Tendsto z atTop atTop:= tendsto_rpow_atTop (show 0<rate from by unfold rate; norm_num)|>.comp (factor_top C)
    have ht := ((tendsto_pow_atTop (show (2:ℕ)≠0 from by decide) |>.comp hz).inv_tendsto_atTop.const_mul (5/2:ℝ))
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (ge_mem_nhds (half_pos he))] with i hh p hp hq η hη hpay
    have hm :0 ≤ startLoss C d p i:=by unfold startLoss; have hz:=invoice_nn (C:=C) d p (i+1); exact mul_nonneg (zero_le_one.trans (stage C _|>.columns_ge)) hz
    have hs :η ≤ barunit (C.S.block i):= (le_mul_of_one_le_left hη (by linarith only [show 1 ≤ stock C i from (stage C _|>.columns_ge)])).trans hpay
    have ht : 0≤ barunit (C.S.block i) := hη.trans hs
    have hC : coordLoss C d p i η ≤ (5/2:ℝ)*barunit (C.S.block i) := by
        unfold coordLoss
        have hv:= smaller d p hp; have hb:=hq.small; rw [mul_comm] at hb
        have hW : (1+invoice d i p (C:=C))*η ≤ 2*barunit (C.S.block i) := by rw [mul_comm, mul_comm (2:ℝ)]; exact mul_le_mul hs (by linarith) (by linarith [invoice_nn (C:=C) d p i]) ht
        have HQ := mul_le_mul hW (show (1+startLoss C d p i)≤5/4 by unfold startLoss; linarith) (by linarith) (by linarith:0≤2*barunit (C.S.block i))
        linarith only [HQ]
    have hx : 0<z i:=Real.rpow_pos_of_pos (show 0 < factor C i from (factor_note C).pos i) _
    refine le_trans (mul_le_mul_of_nonneg_left hC hx.le) (le_trans (?_ : _≤5/2*(z i ^2)⁻¹) hh)
    rw [show barunit (C.S.block i)=(z i)⁻¹ ^3 from rfl]; change z i * _ ≤ _; field_simp; nlinarith [sq_nonneg (2*z i^3)]
lemma live_graph (d:ℕ)(h:Ribbons.Materials C)(γ ε:ℝ)(hγ:0<γ)(hε:0<ε): ∀ᶠ i:ℕ in atTop, ∀ p N:ℕ, ∀ hm:i < N, ∃ (hi:Opened C d i p) (hj:Opened C d (i+1) p),
      (∀ y:C.label d, (F d).coeffSize (fitting d N p (i+1) h.makes hj hm y) ≤ factor C i ^γ * (F d).coeffSize (fitting d N p i h.makes hi hm.le y)) ∧
      ∀ (q : Coefficient (F d) (C.side (i+1) p)) r, reads d N p (i+1) q r → page d p (i+1) q=0 →
    ∃ (v:Coefficient (F d) (C.side i p)) (y:C.label d), reads d N p i v (factor C i ^(-rate)*r) ∧ page d p i v=0 ∧ (factor C i)^rate * (F d).coeffSize (fitting d N p i h.makes hi hm.le y) ≤ ε * r ∧ transition (C:=C) d N p i (value (C:=C) d N p (i+1) q) = value (C:=C) d N p i v + calValues (C:=C) d N p i y := by
    have ht:=(open_late C h.hG d)
    obtain ⟨a,D,u,ψ,W,hv,hI⟩:=h.room
    filter_upwards [ht,(tendsto_add_atTop_nat 1).eventually ht,factor_large C (16:ℝ)⁻¹ (by norm_num),factor_large C γ hγ,coord_tail C d ε hε,feed_tail C h.hG d ε hε] with i hi hj hL h' hv₀ hF p N hm
    refine ⟨hi p,hj p,fun y=>(transfer_cost d N p _ h.makes hm (hi p) (hj p) y).trans (mul_le_mul_of_nonneg_right h'.2 (Work.G08.size_nonneg _ _)),?_⟩
    obtain ⟨η,hη⟩:=hI.listens d N p i (hi p).post hm
    let Y:=factor C i
    have hY :16 ≤ Y:= (inv_inv (16:ℝ)).symm.trans_le hL.1
    obtain ⟨hq,_,_,hη'⟩:=hη.tuned
    intro q r ht hr
    have hr':0≤r:= read_nonneg C ht
    obtain ⟨v,y,hm',hm0,hx,Heq⟩:= stable_step d N p i h.makes hm (hi _) (hj _) hη q ht hr
    refine ⟨v,y,read_weaken C hm' (mul_le_mul_of_nonneg_right (contract_rate C (hi _) (hj _) hY hη' hq) hr'), hm0, le_trans (mul_le_mul_of_nonneg_left hx (show 0≤Y^rate by have : 0≤Y:= (by linarith); exact Real.rpow_nonneg this _)) ?_,Heq⟩
    have h':Y^rate* feedLoss C d p i η ≤ ε :=by unfold Y feedLoss; rw [mul_add]; exact (add_le_add (hv₀ p (hi _) (hj _) η hη' hq) (hF p)).trans_eq (by ring)
    linarith [mul_le_mul_of_nonneg_right h' hr']
end YM.Trace.Physical.GermGraph
