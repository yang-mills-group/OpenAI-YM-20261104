import YM.GapsContact.Power.Rise
/-!
# Regularity of running costs on the graded physical filtration

`Fm` on actual s, all pairs. Want fund within grade. One-step rough with arbitrary broad
stride and arbitrary small gap exponent ε; quotient step matches free in both directions.
Prove closed threshold in all positive lengths. Via operator growth leading on the arcs.
(The logarithmic cost is not necessarily paid when transporting to a fixed norm from ALL scales.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Analysis Extraction Climb Spec Ascent Metric
open Trace Trace.Terrace Trace.Pilot MergeProof.East Next.UVStress Trace.Over
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C: Family G} {d e n:ℕ}{r s:ℝ}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) {H:(Climb.Bel C.book).Hierarchy}{J:Scaling S}{Z:Trace.Terrace.Arch C}
variable (hG:G.Simple)(h : StarPath f H J F.room.kernel 𝓛) (Y:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "K" => C.labels
local notation "T" => Climb.Bel C.book
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "P" => Maxwell.Free.scheme C.labels
local notation "O" => Maxwell.Free.phase_orientation C.labels
local notation "I" => Maxwell.Free.scheme_filters C.labels
local notation "E" => (Climb.Bel C.book).Field
local notation "Q" => F.sector.derivatives
local notation "Hh" => F.room.kernel
local notation "iQ" => F.phase.transport.injection
local notation "oQ" => F.phase.transport.rights

section chips
variable {L:Register G}{T0:Table L}(H:T0.Hierarchy){X:Type*}
lemma chip_real (r:ℝ)(x:T0.Field d)(a:ℝ): chip H d r (a • x)=‖a‖*chip H d r x:=by rw [← Complex.coe_smul,chip_smul,Complex.norm_real]
lemma chip_sum (hr:0<r)(u:Finset X)(w:X→T0.Field d): chip H d r (∑ i∈u,w i) ≤ ∑ i∈u,chip H d r (w i):=by
    induction u using Finset.induction with
    | empty=> simp [chip_zero]
    | insert i t h ih=> rw [Finset.sum_insert h,Finset.sum_insert h]; exact (chip_add H hr ..).trans (add_le_add (le_refl _) ih)
local instance (e:ℕ): FiniteDimensional ℂ (T0.Field e) := inferInstance
-- real comparability. universal geometry on compact ellipsoid, custom upper succ.
def metric_like {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](q p: V→ℝ) : Prop := ∃ c:ℝ,1 ≤ c ∧ ∀ x:V,q x ≤ c*p x
lemma metric_paid {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V](q p : V→ℝ)(hq:Continuous q)(hp:Continuous p)(h₁:∀ (c:ℝ)x, q (c • x)=‖c‖ * q x)(h₂:∀ (c:ℝ)x, p (c • x)=‖c‖ * p x)(h₃:∀ x, x≠0→ 0< p x): metric_like q p:= by
   let P0:= Metric.sphere (0:V) 1
   obtain ⟨b,hb⟩:= ((isCompact_sphere _ _).image_of_continuousOn (show ContinuousOn (q/p) P0 from hq.continuousOn.div hp.continuousOn fun x hx=> (h₃ x (by intro ht; simp[P0,ht] at hx)).ne')).bddAbove
   refine ⟨max 1 b, le_max_left ..,fun x=>?_⟩
   by_cases h:x=0
   · subst x; simp [show q 0=0 by simpa using h₁ 0 0, show p 0=0 by simpa using h₂ 0 0]
   let a:= ‖x‖⁻¹; let y := a • x;have ha:0<a:= inv_pos.mpr (norm_pos_iff.mpr h); have hy:y∈ P0:=by simp [y, P0, norm_smul, Real.norm_of_nonneg ha.le, a, norm_ne_zero_iff.mpr h]
   have hp : q y ≤ b * p y := (div_le_iff₀ (h₃ y (smul_ne_zero ha.ne' h))).1 (hb (mem_image_of_mem (q/p) hy))
   apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (h₃ x h|>.le)); apply le_of_mul_le_mul_left ?_ ha
   rw [h₁ a x,h₂ a x, mul_left_comm b, Real.norm_of_nonneg ha.le] at hp; exact hp
lemma chip_upper (hr:0<r) : metric_like (chip H d r) norm:= by
   letI : FiniteDimensional ℝ (T0.Field d):= Module.Finite.trans ℂ _
   exact metric_paid _ norm (chip_cont H _ r hr) continuous_norm (fun a x=> chip_real H r x a) (fun a x=> norm_smul a x) (fun x h=> norm_pos_iff.mpr h)
lemma chip_lower (hr:0<r)(he:Good H d r): metric_like norm (chip H d r):=by
   letI : FiniteDimensional ℝ (T0.Field d):= Module.Finite.trans ℂ _
   exact metric_paid norm _ continuous_norm (chip_cont H _ r hr) (fun a x=> norm_smul a x) (fun a x=> chip_real H r x a) he
end chips

lemma output_power (d:ℕ): ∃ c:ℝ,1 ≤ c ∧ ∀ r:ℝ,1 ≤ r→∀ x:E d, chip H₀ d 1 (setGear C d r x) ≤ c*r^d*chip H₀ d 1 x := by
   obtain ⟨a,ha,ht⟩:=chip_lower H₀ one_pos (good_blue C d one_pos); have hv:0 ≤ a := zero_le_one.trans ha
   let B:= Extra.FD.recorded C.labels d; let h(i: Fin (B.m+1)) := (B.b.coord i).toContinuousLinearMap
   let c := ∑ i, ‖h i‖* a*chip H₀ d 1 (B.b i)
   refine ⟨max 1 c, le_max_left ..,fun r hr x=>?_⟩;
   have hp(i): ‖h i x‖ ≤ ‖h i‖ * (a*chip H₀ d 1 x):= ((h i).le_opNorm x).trans (mul_le_mul_of_nonneg_left (ht x) (norm_nonneg _))
   have he(i) : chip H₀ d 1 (setGear C d r (B.b i)) ≤ r^d*chip H₀ d 1 (B.b i):= by
      rw [setGear,Pert.Scale.rare,chip_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hr)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr (B.cap i)) (chip_nn ..)
   let v i:= h i x • B.b i; have hx: ∑ i,v i=x:= B.b.sum_equivFun _
   apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans hr) _)) (chip_nn ..))
   nth_rw 1 [← hx]; rw [map_sum]; apply (chip_sum H₀ one_pos ..).trans; unfold c; rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; unfold v; rw [map_smul, chip_smul]
   exact (mul_le_mul (hp i) (he i) (chip_nn ..) (mul_nonneg (norm_nonneg (h i)) (mul_nonneg hv (chip_nn ..)))).trans_eq (by ring)

lemma intake_power (d:ℕ)(ε:ℝ)(he:0<ε): ∀ᶠ r:ℝ in atTop, ∀ x:E d,x≠0 → chip H₀ d r⁻¹ x < r^((d:ℝ)+ε)*chip H₀ d 1 x:=by
   obtain ⟨c,hc,h⟩:= output_power (C:=C) d
   filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_rpow_atTop he).eventually_gt_atTop c] with r hr hh x hx
   have hp:= zero_lt_one.trans hr
   nth_rw 1 [← show setGear C d r⁻¹ (setGear C d r x)=x from (by rw [ahead,inv_mul_cancel₀ hp.ne',ahead_one])]; rw [ahead_cost C (inv_pos.mpr hp)]
   exact lt_of_le_of_lt (h r hr.le x) (mul_lt_mul_of_pos_right (by rw [mul_comm,Real.rpow_add hp,Real.rpow_natCast]; exact mul_lt_mul_of_pos_left hh (pow_pos hp _)) (good_blue C d one_pos x hx))

/- Domain of the power laws. `Offers` includes any unit imaginary budgets as consequences, here not charged. Use pure quotient step both ways (`Firm`). -/
def Ante (d:ℕ)(ε t s:ℝ): Prop := ∀ x:S.Field d, chip F.room.kernel d (s*t⁻¹) x≤ t^((d:ℝ)+ε)*chip F.room.kernel d s x
def Firm (d:ℕ)(ε t s:ℝ): Prop := ∀ x:S.Field (d+1),
    t^((d:ℝ)+1-ε) * sip Hh Q d s x ≤ sip Hh Q d (s*t⁻¹) x ∧ sip Hh Q d (s*t⁻¹) x ≤ t^((d:ℝ)+1+ε)*sip Hh Q d s x

include Y
lemma advent (B : ℝ→Prop) (hv:∀ J:Scaling S, StarPath f H J F.room.kernel 𝓛→ ∀ᶠ i in atTop,B (J.r i)) : ∀ᶠ r in trail, B r:=by
  by_contra hh; obtain ⟨s,hb,hV⟩:= contradictionTrail _ hh; obtain ⟨t,ht,J,hJ,K',hK⟩:= Y.picks s (hb.mono_right nhdsWithin_le_nhds) (fun i=>(hV i).1)
  obtain ⟨i,hi⟩:=(hv J hK.monorail).exists; rw [hJ] at hi; exact (hV (t i)).2 hi

include hG
lemma broad_ante (d:ℕ)(ε:ℝ)(he:0<ε): ∀ᶠ t:ℝ in atTop, ∀ᶠ r in trail,Ante F d ε t r:=by
  filter_upwards [intake_power (C:=C) d ε he,eventually_gt_atTop (0:ℝ)] with t ht hq
  refine advent F Y _ (fun J h=>?_)
  let k:=t^((d:ℝ)+ε); by_contra! hh
  have hv(i) : ∃ j≥i, ∃ x:E d, ‖x‖=1 ∧ k*chip Hh d (J.r j) (J.U j d x)< chip Hh d (J.r j*t⁻¹) (J.U j d x):= by
     obtain ⟨j,hj,H'⟩:= frequently_atTop.mp hh i; unfold Ante at H'; push Not at H'; obtain ⟨x,hx⟩:=H'
     obtain ⟨v,rfl⟩:= (J.U j d).surjective x;
     have hp:v≠0:=by intro h; simp [h,chip_zero] at hx
     let a:ℂ:= (↑‖v‖⁻¹:ℂ); have ha:‖a‖=‖v‖⁻¹:= by simp [a]
     have hA : 0<‖a‖:=by rw [ha,inv_pos]; exact norm_pos_iff.mpr hp
     refine ⟨j,hj,a • v,(by rw [norm_smul,ha]; exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)),?_⟩; rw [map_smul,chip_smul,chip_smul,mul_left_comm k]; exact mul_lt_mul_of_pos_left hx hA
  choose j hj x hx hx' using hv; have hg:Tendsto j atTop atTop:= tendsto_atTop_mono (f:=id) hj tendsto_id
  obtain ⟨v,hv,σ,hσ,hy⟩:= (isCompact_sphere (0:E d) 1).tendsto_subseq (x:=x) (fun i=>by simp [hx])
  let g:=j∘σ
  have ha (a:ℝ)(ha:0<a):= chip_joint F hG h (hg.comp hσ.tendsto_atTop) ha hy
  have he:= le_of_tendsto_of_tendsto' ((ha 1 one_pos).const_mul k) (ha t⁻¹ (inv_pos.mpr hq)) (fun i=> ?_)
  · exact he.not_gt (ht v (fun h=> by simp [h] at hv))
  simpa only [mul_one] using! (hx' (σ i)).le

omit hG Y in
lemma ascentL (d:ℕ)(ε t:ℝ)(he:0<ε)(ht:1<t)(x:E (d+1))(hp:0<sip H₀ P d 1 x):
   t^((d:ℝ)+1-ε)*sip H₀ P d 1 x < sip H₀ P d t⁻¹ x ∧ sip H₀ P d t⁻¹ x < t^((d:ℝ)+1+ε)*sip H₀ P d 1 x:=by
    let s:=t⁻¹; have h0:0<t:=zero_lt_one.trans ht; let z:=sip H₀ P d t⁻¹ x
    have hz:z=t^((d:ℝ)+1)*sip H₀ P d 1 x:=by
       rw [← sip_gain C (inv_pos.mpr h0),Real.rpow_add h0,Real.rpow_natCast,Real.rpow_one,inv_pow,← pow_succ]; change z=_*( (t^(d+1))⁻¹ *z); field_simp [pow_pos h0 _]
    change t^((d:ℝ)+1-ε)*_ < z ∧ z< t^((d:ℝ)+1+ε)*_; rw [hz]; exact ⟨mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt ht (sub_lt_self _ he)) hp,mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt ht (lt_add_of_pos_right _ he)) hp⟩

lemma testing (d:ℕ)(ε t:ℝ)(he:0<ε)(ht:1<t) : ∀ᶠ r in trail, Firm F d ε t r:=by
   have hp:0<t:=zero_lt_one.trans ht; refine advent F Y _ (fun J h=>?_)
   let B(r:ℝ)(x:S.Field (d+1)):= ¬(t^((d:ℝ)+1-ε)*sip Hh Q d r x≤ sip Hh Q d (r*t⁻¹) x ∧ sip Hh Q d (r*t⁻¹) x ≤ t^((d:ℝ)+1+ε)*sip Hh Q d r x)
   have hJ₁:Tendsto J.r atTop trail:=(tendsto_nhdsWithin_iff.mpr ⟨J.drips,Eventually.of_forall J.positive⟩)
   have hJ₂:=secular (J:=J) (m:=id) tendsto_id (inv_pos.mpr hp)
   by_contra! hh
   have hy:= (hh.and_eventually (hJ₁.eventually (stronger F hG Y d))).and_eventually (hJ₂.eventually (stronger F hG Y d))
   let t' i(x:E (d+1)):= J.U i (d+1) x
   let T'(i:ℕ)(x:E (d+1)):= B (J.r i) (t' i x)
   let fZ(i:ℕ)(x:E (d+1)):= (J.U i (d+1)).symm (ridge Hh Q d (J.r i) (t' i x))
   -- ensure witnesses are still high near first measurement
   have hA(i:ℕ):∃ j≥i,∃ x:E (d+1), ‖x‖=1 ∧ T' j x∧ fZ j x=x:=by
      obtain ⟨j,hj,⟨hx,h0⟩,h1⟩:= frequently_atTop.mp hy i; unfold Firm at hx; rw [not_forall] at hx; obtain ⟨v,hv⟩:= hx
      let V:= ridge Hh Q d (J.r j) v; let g:= (J.U j (d+1)); let w:=g.symm V
      have he : g w= V := LinearEquiv.apply_symm_apply ..
      have hl:B (J.r j) V:=by unfold B V; rw [siphoned Hh Q iQ oQ (J.positive j) h0, siphoned Hh Q iQ oQ (mul_pos (J.positive j) (inv_pos.mpr hp)) h1]; exact hv
      have hk:w≠0:=by intro ht; rw [← he,ht,map_zero] at hl; unfold B at hl; simp only [sip,map_zero,chip_zero,mul_zero] at hl; exact hl ⟨le_rfl,le_rfl⟩
      let a:= ‖w‖⁻¹; have ha:0<a:=inv_pos.mpr (norm_pos_iff.mpr hk)
      have hz: g (a • w)=a • V:=by rw [← Complex.coe_smul,map_smul,Complex.coe_smul,he]
      refine ⟨j,hj,a • w,(by rw [norm_smul, Real.norm_of_nonneg ha.le]; exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hk)),?_,?_⟩
      · unfold T'; change B (J.r j) (g _); rw [hz]; unfold B; rw [sip_smul Hh Q, sip_smul Hh Q]; nth_rw 1 [mul_left_comm]; nth_rw 2 [mul_left_comm]; rw [Real.norm_of_nonneg ha.le]; exact fun ⟨u,v⟩=> hl ⟨le_of_mul_le_mul_left u ha,le_of_mul_le_mul_left v ha⟩
      apply g.injective; change g (g.symm (ridge Hh Q _ _ (g _)))=g _; rw [hz,LinearEquiv.apply_symm_apply,map_smul]; exact congr_arg _ (ridge_alt Hh Q iQ oQ (J.positive _) h0 v (J.r j))
   choose j hj x hx hv hw using hA
   obtain ⟨v,h,σ,hσ,hV⟩:= (isCompact_sphere (0:E (d+1)) 1).tendsto_subseq (x:=x) (fun i=>by simp[hx]); rename_i hp' -- rename h ambig. inspect
   let K0:=sip H₀ P d 1 v
   have ht0:= (tendsto_atTop_mono (f:=id) hj tendsto_id).comp hσ.tendsto_atTop
   have h' := nearby_ridge F hG hp' Y ht0 one_pos hV
   have hk : 0 < K0:=by
      have he: ridge H₀ P d 1 v=v:= tendsto_nhds_unique h' (hV.congr fun i=> ?_)
      · unfold K0 sip; rw [he]; exact good_blue C (d+1) one_pos _ (fun hz=>by simp [hz] at h)
      simpa only [mul_one] using! (hw (σ i)).symm
   obtain ⟨hl,hH⟩:=ascentL d ε t he ht v hk
   have hv' := nearby_sip F hG hp' Y ht0 one_pos hV; have hv'':= nearby_sip F hG hp' Y ht0 (inv_pos.mpr hp) hV
   obtain ⟨i,hb,hb'⟩:= (((hv'.const_mul _).eventually_lt hv'' hl).and (hv''.eventually_lt (hv'.const_mul _) hH)).exists
   let W':=t' (j (σ i)) (x (σ i)); apply hv (σ i)
   simp only [mul_one] at hb hb'; exact ⟨hb.le,hb'.le⟩

lemma both_broad (d:ℕ)(ε:ℝ)(he:0<ε): ∀ᶠ t:ℝ in atTop, ∀ᶠ r in trail, Ante F d ε t r ∧ Ante F (d+1) ε t r ∧ Firm F d ε t r:= by filter_upwards [eventually_gt_atTop (1:ℝ),broad_ante F hG Y d ε he,broad_ante F hG Y (d+1) ε he] with t ht h₁ h₂; exact h₁.and (h₂.and (testing F hG Y d ε t he ht))
end YM.GapsContact.Power
