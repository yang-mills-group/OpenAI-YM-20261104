import YM.RG20.Borders
import YM.Pert.Asymptotics.RawAxis
/-!
# Insertions charged on patches, all backgrounds

Scene includes all flags, complete unmarked K costs and shared vacuum divisor.
Use Therm.homes and slot consistency to gain a model on arbitrarily large polynomial
patches with *every* source tested at once in that geometry, not assuming anything small on
those marks, only paying the actual local supports and amplitudes. The patch here is at a
single mesh (any k ≤ N); no small bound of conditional law required in arbitrary outside geometry.
The approximate patch bill is a SUBprobability receipt (zero if local-normalization vanishes;
that sector paid by the new estimate too).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG20
open Function Filter Set MeasureTheory Lattice Wilson RG OPE.Therm House Portolan
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n : Side}
section local_price
variable {A : Finset (Edge (Site n))} {f : Config G n → ℝ} {R : Rep G n} {r q t:ℕ} {τ C e s:ℝ} {z:Site n}
local notation "W" => essence R r τ q z
lemma parcel_ge : q ≤ Portolan.parcel R r q := by unfold parcel; omega
lemma attempts (Y : Stove.Chart R r C e) (h : Portolan.parcel R r q ≤ t)
    (ho : fence (coat t z) f) (hx : A ⊆ coat q z)
    (hf : Measurable f) (ha:0<s) (hb:∀ U,‖f U‖ ≤ s) :
    Attempt R r τ t z (fun U=>(2*s)⁻¹*(f U-recoup A (essence R r τ q z) f U)) A := by
   let F:=fun U=> f U-recoup A W f U
   have ht: Envelope f:=⟨hf,s,hb⟩
   have he : Envelope W:= essence_env Y; have hy : Envelope (recoup A W f):=recoup_env he essence_nonneg ht
   have hp: fence (coat t z) (recoup A W f):= recoup_fence ho (essence_fenced Y h)
   have hh : q≤ t:= parcel_ge.trans h
   refine ⟨?_
      ,fun U V hv=>?_, fun U=>?_, measurable_const.mul (hf.sub hy.meas),fun U=>?_⟩
   · -- 
     exact hx.trans (coat_extend z hh)
   · rw [ho U V hv,hp _ _ hv]
   · simp only [norm_mul,norm_inv,Real.norm_of_nonneg (mul_pos zero_lt_two ha).le]; rw [inv_mul_le_iff₀ (by positivity),mul_one]; apply (norm_sub_le ..).trans; exact (add_le_add (hb U) (recoup_bound he essence_nonneg hb hf U)).trans_eq (two_mul _).symm
   obtain ⟨g,hg,_,_,he'⟩:= collared (τ:=τ) Y hx hh
   have hK : press A (fun U=> F U * W U) U = 0 := centered_press he essence_nonneg ht U
   rw [he',show (fun U=>(2*s)⁻¹ * F U * (g U * W U))=(fun U=> ((2*s)⁻¹*g U)*(F U*W U)) from funext fun U=>by ring,
      pressmulL (fun U=> F U*W U) (X:=A) (h:=fun U V hv=>congr_arg (fun x:ℝ=>(2*s)⁻¹*x) (hg _ _ hv)),hK,mul_zero]

end local_price

variable {H:History G} (Z:H.Selected) {i N p t m q:ℕ} {z:Site (H.S.side i p)} {τ C e:ℝ}
local notation "Q" => H.rep N p i
local notation "𝒞" => Config G (H.S.side i p)
local notation "η" => prior G (H.S.side i p)
local notation "V" => H.levels
local notation "D" j => scene H N p j
local notation "X" => H.levels.clock.hatBeta i
local notation "r" => burning H.levels i
local notation "W" => (essence (H.rep N p i) (burning H.levels i) τ q z)

variable (Y:Stove.Chart (H.rep N p i) (burning H.levels i) C e) (hm:Homes H m i)
    (hN:i≤ N) (hC:cool H.levels i ≤ τ) (hX: 2*τ ≤ (H.rep N p i).p.threshold)
    (hy:Portolan.parcel (H.rep N p i) (burning H.levels i) q ≤ t) (ht:(t:ℝ)≤H.levels.clock.hatBeta i^m)
    {A:Finset (Edge (Site (H.S.side i p)))}
    (he:A ⊆ coat q z)
include Z Y hm hN hC hX hy ht he
local notation "β" => (H.levels.clock.hatBeta i)
set_option maxHeartbeats 400000 in
lemma local_patch (f:Config G (H.S.side i p)→ ℝ)(hf: Measurable f)(hb:fence (coat t z) f) (s:ℝ)(hs:∀ U,‖f U‖≤ s) :
    ‖(∫ U,f U∂ (D i))-(∫ U,recoup A W f U∂ (D i))‖ ≤ 2*s* (β^m)⁻¹:=by
   have hS : 0 ≤ s:= (norm_nonneg (f 1)).trans (hs 1)
   by_cases h:s=0
   · subst s; rw [show f=(fun _=>0) from funext fun i=> norm_eq_zero.mp (le_antisymm (hs i) (norm_nonneg _))]; simp [recoup, press]
   have hx:= lt_of_le_of_ne hS (Ne.symm h); have hF: Envelope f := ⟨hf,s,hs⟩
   let F:= recoup A W f; have hh : Envelope F:= recoup_env (essence_env Y) essence_nonneg hF
   letI:= probability (p:=p) Z hN
   have hp:= hm N p hN t ht τ hC hX z _ A (attempts Y hy hb he hf hx hs)
   rw [integral_const_mul,integral_sub (hF.integrable _) (hh.integrable _),norm_mul,norm_inv,Real.norm_of_nonneg (by positivity : 0 ≤ 2*s), inv_mul_le_iff₀ (by positivity)] at hp
   exact hp

-- Every sector by pointwise truncation of the *integrand* f evaluated on the model only.
-- Bill with exact `ESSENCE` denominator (do not divide by any eligible-packet K).
omit Z hm Y hN hC hX hy ht he in
lemma healthy_only (h : τ≤(Q).p.threshold) (f:Config G (H.S.side i p)→ ℝ) :
    recoup A W (masked (Q).p.threshold (region q z) f)=recoup A W f:=by
   have hp(U): (masked (Q).p.threshold (region q z) f U)*(W U)= f U*(W U):=by
      by_cases he: W U=0
      · simp_rw [he,mul_zero]
      rw [masked_eq _ _ _ _ (chilled_health h U he)]
   unfold recoup; simp_rw [hp]
lemma not_paid_cost :
    MeasurableSet {U:Config G (H.S.side i p) | press A W U =0} ∧
    (D i).real {U:Config G (H.S.side i p) | press A W U=0} ≤ 2*(β^m)⁻¹ := by
    let c:= W; let f:= (fun _:𝒞 => (1:ℝ))
    letI:= probability (p:=p) Z hN
    let S:= {U:𝒞| press A W U=0}; have hh: MeasurableSet S:= (held_mass A (essence_env Y)|>.meas) (measurableSet_singleton 0)
    have hn:recoup A W f = Set.indicator Sᶜ f :=by
       funext U; by_cases he: press A W U=0 <;> simp [f,S,recoup,he,Set.indicator]
    refine ⟨hh,?_⟩
    have hp:=local_patch Z Y hm hN hC hX hy ht he f measurable_const (fun _ _ _=>rfl) 1 (fun _=> (norm_one (α:=ℝ)).le)
    rw [hn,integral_indicator hh.compl] at hp
    simpa [f, measureReal_compl hh, abs_of_nonneg measureReal_nonneg] using hp -- name
end YM.RG20
