import YM.RG20.Recoup
/-!
# Real-history patch estimation with complex sources
 Retain absolute cost on *any measurable local observable* (thus all tested sign and shape choices
 as long as one joint support and amplitude fit). No unit reserve for unseen terms.
 Normalize by the same real local denominator. Error weight in the next file at arbitrary κ
 in running units (not derivative order); no charge per-site from denominator divisions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG20
open Function Filter Set MeasureTheory Lattice Wilson RG OPE.Therm House Portolan
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius

section
variable {G : Gauge} {n : Side} {f : Config G n→ℂ} {A B : Finset (Edge (Site n))}
  {w : Config G n→ℝ} {q : ℝ}
local notation "η"=> prior G n

-- use Bochner on components. common patch state, for any measurable bounded complex product.
def snorkel (A : Finset (Edge (Site n))) (w : Config G n→ℝ) (f : Config G n→ℂ) (U : Config G n) :=
    (press A w U)⁻¹ • ∫ V, w (meld A V U) • f (meld A V U) ∂η

local notation "Ψ"=> snorkel A w
variable (h:∀ U,0 ≤ w U)(hw:Envelope w)
lemma snorkel_still : stills A (snorkel A w f):=by
   intro U V hp; unfold snorkel; rw [dormant A w U V hp]
   apply congr_arg; apply integral_congr_ae; refine Eventually.of_forall fun x=> ?_
   have he: meld A x U=meld A x V:=by funext i; unfold meld; by_cases h:i∈A <;> simp only [h,↓reduceIte]; exact hp (show i ∈ (↑(Aᶜ : Finset _):Set _) from Finset.mem_compl.mpr h)
   dsimp only; rw [he]
lemma snorkel_site (h : fence B f)(hw : fence B w) : fence B (snorkel A w f):=by
   intro U V hx; unfold snorkel; rw [pressed_fence hw U V hx]; apply congr_arg; apply integral_congr_ae; filter_upwards with W
   have hz: EqOn (meld A W U) (meld A W V) B:= by
     intro i he; unfold meld; by_cases h:i∈A <;> simp only [h,↓reduceIte]; exact hx he
   rw [hw _ _ hz,h _ _ hz]

include hw
lemma snorkel_commute (hf:Envelope f) (g:ℂ→L[ℝ]ℝ)(U:Config G n): g (snorkel A w f U)=recoup A w (fun x=>g (f x)) U:=by
   let W:= fun U=> (w U:ℂ)*f U
   have hF: Integrable (fun V=> w (meld A V U) • f (meld A V U)) η:=by
      simp_rw [Complex.real_smul]; exact ((Envelope.mulC (Envelope.ofReal_env hw) hf).comp_env (meld_meas measurable_id measurable_const)).integrableC _
   unfold snorkel; rw [map_smul, ← g.integral_comp_comm hF]; simp_rw [map_smul,smul_eq_mul]; rw [inv_mul_eq_div]; congr 1; apply integral_congr_ae; filter_upwards with V; rw [mul_comm]; -- see
lemma snorkel_env (hf:Envelope f) : Measurable (snorkel A w f):=by
   have ht: Envelope (fun p: Config G n × Config G n=> (w (meld A p.2 p.1):ℂ)*f (meld A p.2 p.1)):= (Envelope.mulC (Envelope.ofReal_env hw) hf).comp_env (meld_meas measurable_snd measurable_fst)
   apply (held_mass A hw).meas.inv.smul (show Measurable (fun U=> ∫ V,w (meld A V U) • f (meld A V U) ∂η) from ?_)
   simp_rw [Complex.real_smul]; exact ht.meas.stronglyMeasurable.integral_prod_right'.measurable
include h in
lemma snorkel_bounds (_he:Measurable f) (hF:∀ U, ‖f U‖ ≤ q) (U:Config G n) : ‖snorkel A w f U‖ ≤ q:=by
   have hB :0≤ q:= (norm_nonneg _).trans (hF U)
   have hx := positive_bill h (A:=A) U
   unfold snorkel; by_cases hh:press A w U=0
   · rw [hh,inv_zero,zero_smul,norm_zero]; exact hB
   rw [norm_smul, norm_inv, Real.norm_of_nonneg hx, inv_mul_le_iff₀ (lt_of_le_of_ne hx (Ne.symm hh))]
   rw [press,← integral_mul_const]; apply (norm_integral_le_integral_norm _).trans
   apply integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) _ (Eventually.of_forall fun _=>?_) -- holes
   · exact ((enclosed hw (meld_meas measurable_id measurable_const)).integrable _).mul_const q
   dsimp only; rw [norm_smul, Real.norm_of_nonneg (h _)]; exact mul_le_mul_of_nonneg_left (hF _) (h _)

-- version certifying SAME absolute ratio accounting for all flags, zero if unsupported
omit hw in
lemma mask_snorkel {R:Rep G n} {r q₀:ℕ}{τ:ℝ}{z:Site n}(ht:τ ≤ R.p.threshold) :
    snorkel A (essence R r τ q₀ z) f=snorkel A (essence R r τ q₀ z) (masked R.p.threshold (region q₀ z) f):= by
      funext U; unfold snorkel; apply congr_arg; apply integral_congr_ae; filter_upwards with V
      by_cases h: essence R r τ q₀ z (meld A V U)=0
      · simp_rw [h,zero_smul]
      rw [masked_eq _ _ _ _ (chilled_health ht _ h)]
end
section
variable {G:Gauge}{H:History G} (Z:H.Selected) {i N p t m q:ℕ} {z:Site (H.S.side i p)} {τ C e:ℝ}
local notation "Q" => H.rep N p i
local notation "𝒞" => Config G (H.S.side i p)
local notation "V" => H.levels
local notation "D" j=> scene H N p j
local notation "r" => burning H.levels i
local notation "W" => (essence (H.rep N p i) (burning H.levels i) τ q z)

variable (Y:Stove.Chart (H.rep N p i) (burning H.levels i) C e) (hm:Homes H m i)
    (hN:i≤ N) (hC:cool H.levels i ≤ τ) (hX: 2*τ ≤ (H.rep N p i).p.threshold)
    (hy:Portolan.parcel (H.rep N p i) (burning H.levels i) q ≤ t) (ht:(t:ℝ)≤H.levels.clock.hatBeta i^m)
    {A:Finset (Edge (Site (H.S.side i p)))}
    (he:A ⊆ coat q z)
include Z Y hm hN hC hX hy ht he
local notation "β" => (H.levels.clock.hatBeta i)
lemma patchSea (f:Config G (H.S.side i p)→ ℂ)(hf: Measurable f)(hb:fence (coat t z) f) (s:ℝ)(hs:∀ U,‖f U‖≤ s) :
    ‖(∫ U,f U∂ (D i))-(∫ U,snorkel A W f U∂ (D i))‖ ≤ 4*s* (β^m)⁻¹:=by
   letI:= probability (p:=p) Z hN; let K:=snorkel A W f; have hw:Envelope W:= essence_env Y
   have hp:Envelope f:= ⟨hf,s,hs⟩; have hP:Envelope K:=⟨snorkel_env hw hp,s,snorkel_bounds essence_nonneg hw hf hs⟩
   let a:=(∫ U,f U∂ (D i))-(∫ U,K U∂ (D i)); let x:=2*s*(β^m)⁻¹
   have h(g:ℂ→L[ℝ]ℝ)(hv:∀ i:ℂ,‖g i‖≤‖i‖): ‖g a‖≤ x:=by
      unfold a; rw [map_sub, ← g.integral_comp_comm (hp.integrableC _), ← g.integral_comp_comm (hP.integrableC _)]
      unfold K; simp_rw [snorkel_commute hw hp]; exact local_patch Z Y hm hN hC hX hy ht he _ (g.continuous.measurable.comp hf) (fun i j h=> congr_arg g (hb i j h)) s (fun U=> (hv _).trans (hs U))
   refine (Complex.norm_le_abs_re_add_abs_im a).trans ((add_le_add (show |a.re| ≤ x from h Complex.reCLM Complex.abs_re_le_norm) (show |a.im| ≤ x from h Complex.imCLM Complex.abs_im_le_norm)).trans_eq ?_); unfold x; ring
end
end YM.RG20
