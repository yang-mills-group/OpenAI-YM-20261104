import YM.MatchingLedger.Periodical.Exposure

/-!
# Forecast funded post-L, exact log-pressure entry requirement and coupling bills

Proof manipulates all pressures on bounded observables at finite volume only. Includes the
exceptional/exterior bill needed here, det/kinetic & field normalization to be bought
separately before any use in Wilson frame transport.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset

section pressure
variable {U : Type} [MeasurableSpace U]{μ : Measure U}[IsProbabilityMeasure μ] {f X S : U→ℝ}{q Q z t L : ℝ} {A : Set U}
variable (hf : Weight μ f)(ht:Envelope S)(he : Envelope X)
lemma weigh_sub (ht: Envelope f) (hp : Envelope X)(hv:Envelope S) : weigh μ f (fun z=> X z- S z)=weigh μ f X - weigh μ f S := by
  unfold weigh; simp_rw [sub_mul]; rw [integral_sub ((hp.mul ht).integrable μ) ((hv.mul ht).integrable μ),sub_div]
include hf in
omit [IsProbabilityMeasure μ] in
lemma importance : ‖weigh μ f X‖≤ weigh μ f (fun x=> ‖X x‖) := by
  have hp := hf.nonempty
  unfold weigh; rw [norm_div,Real.norm_of_nonneg hp.le]; apply div_le_div_of_nonneg_right _ hp.le; apply (norm_integral_le_integral_norm ..).trans_eq
  apply integral_congr_ae; filter_upwards with x; rw [norm_mul, Real.norm_of_nonneg (hf.positive _)]
include hf ht he
lemma blister (hq:0≤q)(hQ:0≤Q)(hA:∀ v∈A, ‖X v‖≤q)(he':∀ v, ‖X v‖≤Q)(hp:∀ v, v∉ A→ t≤ S v) (hm:pressureBill μ f S≤L) :
    ‖weigh μ f X‖ ≤ q+ Q*Real.exp (L-t) := by
 let g:= fun v=> Real.exp (S v); let a:=Q*Real.exp (-t)
 have hpos :0≤ a:= mul_nonneg hQ (Real.exp_pos _).le; have hg:=ht.exp; have h0 := hf.toEnvelope
 have hj(x) : ‖X x‖ ≤ q+a*g x := by
   by_cases hw:x∈ A
   · exact (hA x hw).trans (le_add_of_nonneg_right (mul_nonneg hpos (Real.exp_pos _).le))
   refine (he' x).trans ?_
   refine le_trans (le_trans (b:= a*g x) ?_ (le_rfl)) (le_add_of_nonneg_left hq); unfold a g; rw [mul_assoc]; refine le_mul_of_one_le_right hQ ?_; rw [← Real.exp_add]; apply Real.one_le_exp; have h:=hp x hw; linarith
 have he0 : Envelope (fun x=>‖X x‖):= envelope_repaired he continuous_norm
 have ha : Envelope (fun v=> a * g v):= (Envelope.const _).mul hg
 have hx:= Real.exp_monotone hm; unfold pressureBill at hx; rw [Real.exp_log (weigh_exp_pos hf ht)] at hx
 apply (importance hf).trans; apply (weigh_mono hf he0 ((Envelope.const _).add ha) hj).trans
 rw [weigh_add h0 (Envelope.const _) ha, weigh_const hf, weigh_const_mul]
 apply add_le_add le_rfl; exact (mul_le_mul_of_nonneg_left hx hpos).trans_eq (by unfold a; rw [mul_assoc, ← Real.exp_add]; congr 2; ring)
end pressure

variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    {A : ChartRatio G} (Y : Chip (Page G c)) {t Z : ℝ} (i : Needle F G)(k d : ℕ) (H : Budget G A (d+3))
variable (ht:1≤t)(hZ:1≤Z)(hY:‖Y‖≤ Z)
variable {R : Support c}
    (hr : t⁻¹*Z≤dial A) (hh:t⁻¹*Z ≤ H.space S.patch S.kernel)
    (hh' : t⁻¹* Z/(4*H.pale) ≤ H.glow)
    (p : Token (Needle F G))(hd : heft p≤d)(he:k≤d)
    (hR:arc F (Sum.inl i) ⊆ R)(hp:p.support⊆ located (nest F) R)
local notation "a" => (t⁻¹*Z)
local notation "Y'" => t⁻¹ • Y
local notation "ι" => Needle F G
local notation "I" => Sum.inl i
local notation "V" => edition F s A Y
local notation "M" => H.income S.patch S.kernel
local notation "ξ" => fieldTest (G:=G) F R
local notation "P" => notice F s Y i k (mark p) A t
local notation "E" => milled F s A (Y') t a R i (mark p)
local notation "J" => run F A t P
local notation "w" => Cooling.weight F (runway (t⁻¹ • Y)) t
local notation "ω'" => F.order G
local notation "W" => weigh (F.order G) w

section shape
include hZ ht hh'
lemma recoil {U : F.Slice G}(hf:U ∉ ξ (a/4)) : (Z/(4*H.pale))^2 ≤ Cooling.shock F R t U := by
  have ht':0<t:= zero_lt_one.trans_le ht; have hp:0<H.pale:= H.law.1; have he:0<Z:= zero_lt_one.trans_le hZ
  obtain ⟨i,h,hk⟩: ∃ i : F.Free, area F i∈R ∧ U i∉sector G (a/4) := by unfold fieldTest at hf; simpa using hf
  have hv:t⁻¹*Z/(4*H.pale) ≤ G.chord (U i):=by
    apply le_of_not_gt; intro hw
    have hz := H.law.2.2 _ (hw.le.trans hh'); apply hk; refine ⟨_, mem_ball_zero_iff.mpr (hz.2.trans_lt ?_), hz.1⟩ -- wait le_trans strict? `.trans_lt`
    rw [mul_comm H.pale]; apply (lt_div_iff₀ hp).mp; exact hw.trans_eq (by ring)
  refine le_trans (b:= t^2* G.chord (U i)^2) ?_ ?_
  · apply le_trans (b:= t^2*(t⁻¹*Z/(4*H.pale))^2) (le_of_eq ?_) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hv _) (sq_nonneg _)); field_simp
  unfold Cooling.shock total links; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); rw [total_at]; rw [← F.off_tree U i]; exact Finset.single_le_sum (s:=located (region (α:=Axis) S) R) (f:=fun i=>G.chord (F.drape U i)^2) (fun i _=>sq_nonneg _) (loc.mpr h)

include hB hh hr hY he hd hR hp
lemma amount (q L : ℝ) (hq:0≤q)(h:pressureBill ω' w (fun x=> q*Cooling.shock F R t x) ≤ L) :
    ‖W J‖ ≤ (Z^d)*(park (belt S.patch) * (2*M*Z^(k+2))) * (t⁻¹)^(k+1) + proximity G S.patch M t Z d * Real.exp (L- q*(Z/(4*H.pale))^2) := by
  have hm:0≤M:=zero_le_one.trans (H.income_one ..); have hZ':0<Z:=zero_lt_one.trans_le hZ; have ht':0<t:=zero_lt_one.trans_le ht
  have hv:‖t⁻¹ • Y‖ ≤ a:=by rw [norm_smul_of_nonneg (inv_pos.mpr ht').le]; exact mul_le_mul_of_nonneg_left hY (by positivity)
  have hm':0<t⁻¹*Z:= by positivity
  have hf:= Cooling.weight_pass F (runway (Y')) t hB
  obtain hE : W E=0:= sprig F s hB i (mark p) H ht' hm' hr hv hh hR
  have hJ : Envelope J := run_pass ..
  have hh': Envelope E:= milled_pass F s (Y') t a R i (mark p) H hr hv hh -- shadow
  have hx : W J= W (fun x=> J x-E x):= by rw [weigh_sub hf.toEnvelope hJ hh',hE,sub_zero]
  rw [hx]; refine blister (A:=ξ (a/4)) (S:=fun x=> q*Cooling.shock F R t x) hf ((Envelope.const _).mul (Cooling.bounded F R t)) (envelope_sub hJ hh') (by positivity [park_nn (belt S.patch)]) (prox_ge G S.patch ht'.le hm hZ'.le _) ?_ ?_ ?_ h
  · intro x hx; exact quiet F s hB Y i k d H ht hZ hY hr hh hR he p hd hx hp -- order check
  · intro x; exact bump_bill F s hB Y i k d H ht hZ hY hr hh p hd he x
  intro x hx; exact mul_le_mul_of_nonneg_left (recoil F d H ht hZ (by assumption) hx) hq
end shape

section solar
-- actual identity uses scaled log inputs (x=t*angle bits on this A) at the top step. α powers convention.

def pigment (A : ChartRatio G) (t : ℝ) : Prediction (Needle F G) where
  toFun p:= weigh (F.order G) (Cooling.weight F (runway (t⁻¹ • Y)) t) (run F A t p)
  map_add' p q := by
    unfold run; simp_rw [_root_.map_add]; exact weigh_add (Cooling.weight_pass F (runway (t⁻¹ • Y)) t hB).toEnvelope (run_pass F A t p) (run_pass F A t q)
  map_smul' u p := by unfold run; simp_rw [_root_.map_smul]; exact weigh_const_mul ..
lemma pigment_one : pigment F hB Y A t 1=1:=by
  change W (run F A t 1)=_; unfold run; simp_rw [read_apply,_root_.map_one]; exact weigh_self_unit _ (Cooling.weight_pass F _ _ hB)

-- stamp computed uniformly post-L. prices powers explicit (use with construction eventually).

def curve (i : Needle F G)(p : Token (Needle F G)) : Support c:= arc F (.inl i) ∪ p.support.image (nest F)
def acres (P' : Patch) (d : ℕ) := d+ (stretch P'+stretch P'+1)^4
include hd in
lemma space_curve : (curve F i p).card ≤ acres S.patch d := by
  have he : p.support.card ≤ d:= le_trans (b:=heft p) ?_ hd
  · apply le_trans (Finset.card_union_le ..); unfold acres; rw [Nat.add_comm d]; exact Nat.add_le_add (mag (atlas F I) (stretch S.patch)) (Finset.card_image_le.trans he)
  calc _ = ∑ _i∈p.support,(1:ℕ) := by simp
       _ ≤ _ := Finset.sum_le_sum (fun i hi=> Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
lemma covary : p.support⊆located (nest F) (curve F i p) := fun _ hj=> loc.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))

local notation "L" => lowerCost G S.patch S.kernel
local notation "B" => proximity G S.patch M t Z d
-- post actual step certificate. keep normalization and rank/everything visible.
include hr hh hh' hZ ht hB hY

def holdRequest (p : Patch)(v Z : ℝ)(d : ℕ) := 1+Z^d*park (belt p)*(2*v* Z^(d+2))

variable {u c' T : ℝ}
-- easier not repeating normalization everywhere in schedule, package Prop with cost expressions.
structure Dated {A:ChartRatio G}(H : Budget G A (d+3)) (Y : Chip (Page G c)) (t Z u q B' : ℝ) : Prop where
  fire : 1≤t
  earn : 1≤Z
  background : ‖Y‖≤Z
  sky : t⁻¹*Z≤dial A
  script : t⁻¹*Z ≤ H.space S.patch S.kernel
  shrink : t⁻¹*Z/(4*H.pale) ≤ H.glow
  unit : B' ≥ tableFare G S.patch S.kernel (H.income S.patch S.kernel) d * Z^(d+1)
  paid : holdRequest S.patch (H.income S.patch S.kernel) Z d ≤ B'
  u_pos : 0 ≤ u -- log factor per site
  q_pos : 0 ≤ q
  enough : proximity G S.patch (H.income S.patch S.kernel) t Z d * Real.exp (acres S.patch d * u - q*(Z/(4*H.pale))^2) ≤ (t⁻¹)^(d+1)
  calm : ∀ (F : Forest S.ratio) (R : Support c), pressureBill (F.order G)
        (Cooling.weight F (runway (t⁻¹ • Y)) t) (fun x=> q*Cooling.shock F R t x) ≤ R.card * u

omit hr hh hh' hZ ht hY
lemma sufficient (h:Dated (S:=S) d H Y t Z u c' T) (hd':heft p≤d)(hk:k≤d) :
    ‖Books.FPS.ley V i (fun _=> pigment F hB Y A t) (mark p) t⁻¹ k‖ ≤ T*(t⁻¹)^(k+1):= by
  rw [← merge_notice]; change ‖W J‖ ≤ _; let R:= curve F i p
  have h0:= h.fire; have ha : 0<t⁻¹ := inv_pos.mpr (zero_lt_one.trans_le h0); have hZ:= h.earn
  have he : 0 ≤ M:= zero_le_one.trans (H.income_one ..)
  have hv := amount (R:=R) F s hB Y i k d H h0 hZ h.background h.sky h.script h.shrink p hd' hk (Finset.subset_union_left (s₂:=p.support.image (nest F))) (covary F i p) c' ((acres S.patch d:ℝ)*u) h.q_pos ((h.calm F R).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (space_curve F i d p hd')) h.u_pos))
  refine hv.trans (_root_.le_trans (b:=holdRequest S.patch M Z d *(t⁻¹)^(k+1)) ?_ (mul_le_mul_of_nonneg_right h.paid (by positivity)))
  unfold holdRequest; rw [add_mul,add_comm (1*_ : ℝ), one_mul]
  apply add_le_add (mul_le_mul_of_nonneg_right ?_ (by positivity)) (h.enough.trans <| pow_le_pow_of_le_one ha.le (inv_le_one_of_one_le₀ h0) (by omega))
  rw [mul_assoc (_^_ : ℝ)]; gcongr; exact park_nn _
lemma solar (hs : InRange S) (h:Dated (S:=S) d H Y t Z u c' T) (p : Poly (Needle F G)) (l : ℕ)(hp':p.totalDegree≤l)(hk:k+l≤d) :
    let v:= V; let B' := stamp F s hB hs A Y
    ‖W (run F A t p) - Books.FPS.forecast B' t⁻¹ k p‖ ≤ fare p * (Books.FPS.bill d T k l * (t⁻¹)^(k+1)) ∧
      ‖Books.FPS.report v B' k p‖≤ fare p*Books.FPS.bill d T k l:= by
  have hp := license_earn F s hB hs Y H d (by omega) Z h.earn h.background h.unit
  exact ⟨hp.invoice (pigment F hB Y A t) (inv_pos.mpr (zero_lt_one.trans_le h.fire)).le (pigment_one F hB Y) (fun q p hq i=> sufficient F s hB Y i q d H p h (by omega) (by omega)) _ _ _ hp' hk,hp.formal_cost _ _ _ hp' hk⟩
end solar
end YM.MatchingLedger.Periodical
