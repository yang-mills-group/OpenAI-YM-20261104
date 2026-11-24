import YM.GradedFar.TrueCost
/-!
# G6 on the receding physical measurements. Apply also at the actual Tower H.

This proves these physical estimates from the indicated **LogTrace and QScale (G.2)** costs,
directly on Final & Reader. Does not assume compact/gridded MS comparison to infer them.
Log powers here on both lengths, eventually collapse to a *fixed* (independent of B!) cost in g
owning the eventual assertions separately (budget includes B only in onset). The derivation of `G6` uses these hypotheses independently of `G9`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar
open Fork (Setting Coat)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower S)
    {n m:ℕ} (d:Fin n→ℕ) (e:Fin m→ℕ)(h:ℕ)
local notation "g" => strength G

section Geometry
variable {K:Set (Points n)}{S':Set (Points m)} (hK:IsCompact K)(hx:K ⊆ conf n)(hS:IsCompact S')(hy:S'⊆Outside m)
include hK hx hS hy
lemma setup : ∃ M δ, 0≤M ∧ 0<δ ∧ ∀ x∈K, ∀ y∈S', Setting M δ x.ofLp y.ofLp := by
  obtain ⟨M,hM,a,ha,hA⟩:= compact_within K hK hx
  obtain ⟨M',hm,b,hb,hB⟩:= compact_within (outgoing '' S')
    (hS.image (show Continuous _ from (continual continuous_const continuous_id : Continuous (outgoing (m:=m)))))
    (image_subset_iff.mpr hy)
  refine ⟨max M M', min a (b/2),hM.trans (le_max_left ..), lt_min ha (half_pos hb),fun x hk y hs=>?_⟩
  specialize hA x hk; specialize hB _ (mem_image_of_mem outgoing hs); constructor
  · intro i; have hh:=hA.span i; simp only [sub_zero,mul_one] at hh; exact hh.trans (le_max_left ..)
  · intro i; have hh:=hB.span (Fin.natAdd 1 i); simp only [sub_zero,mul_one] at hh
    change ‖outgoing y (Fin.natAdd 1 i)‖ ≤ _ at hh; rw [outgoing,forest_right] at hh; exact hh.trans (le_max_right ..)
  · intro i j hi; have ht:=hA.spaced i j hi; rw [mul_one] at ht; exact (min_le_left ..).trans ht
  · intro i j hi; have ht:=hB.spaced (Fin.natAdd 1 i) (Fin.natAdd 1 j) ((Right 1 m).injective.ne hi); rw [mul_one] at ht
    change _ ≤ ‖forest (0:Points 1) y (Fin.natAdd 1 i)-forest (0:Points 1) y (Fin.natAdd 1 j)‖ at ht
    rw [forest_right, forest_right] at ht; exact (min_le_right ..).trans ((half_le_self hb.le).trans ht)
  intro i
  have ht:= hB.spaced (Fin.natAdd 1 i) (Fin.castAdd m (0:Fin 1)) (Ne.symm (opposite _ _))
  rw [mul_one] at ht; change _ ≤ ‖forest (0:Points 1) y (Fin.natAdd 1 i)-forest (0:Points 1) y (Fin.castAdd m (0:Fin 1))‖ at ht
  rw [forest_left,forest_right] at ht; simpa only [PiLp.zero_apply,sub_zero] using (le_trans
    (show 2 * min a (b/2) ≤ b from by linarith only [min_le_right a (b/2)]) ht)
end Geometry

variable (hG:G.Simple) {U B:ℝ}
include hG
/-- uniformly exercising a cost **at length s** (still eventually r). Valid also later on deriving detector.
Don't use `∀ s, ∃ r` pointwise-little-oh and then secretly exercise at varying points. -/
lemma out_radius (P:ℝ→ Prop) (h:∀ᶠ s:ℝ in trail, P s) : ∀ᶠ r:ℝ in trail,
    ∀ T:ℝ,1 ≤ T → T ≤ U*(g r)^(-B) → P (r*T) := by
  let A:=max 1 U
  obtain ⟨p,hp⟩:= exists_nat_gt B
  have hq:= sub_pos.mpr (lt_of_eq_of_lt (b:= (B:ℝ)) rfl hp : B<p) -- ensure cast
  have hx:Tendsto (fun r=> A*(g r)^((p:ℝ)-B)) trail (𝓝 0) := by
    have h0:Tendsto (fun r=>(g r)^((p:ℝ)-B)) trail (𝓝 0):= by
      simpa only [Real.zero_rpow hq.ne', Function.comp_def] using
        ((Real.continuousAt_rpow_const 0 ((p:ℝ)-B) (Or.inr hq.le)).tendsto.comp
          (Coupling.conforms hG (strength_coupling hG)))
    simpa only [mul_zero] using h0.const_mul A
  obtain ⟨b,hb,hB⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp h
  filter_upwards [hx.eventually (gt_mem_nhds hb),self_mem_nhdsWithin,strength_positive hG,radius_falls hG p]
    with r hr (hz:0<r) ht hv T hT HF
  have Ha: 0<A:=lt_of_lt_of_le zero_lt_one (le_max_left ..); apply hB; refine ⟨mul_pos hz (zero_lt_one.trans_le hT),?_⟩
  apply le_trans _ hr.le; rw [Real.rpow_sub ht, Real.rpow_natCast]; rw [Real.rpow_neg ht.le] at HF
  calc _≤ (g r)^p*T:=by gcongr
       _≤ (g r)^p*(A*((g r)^B)⁻¹):= mul_le_mul_of_nonneg_left (HF.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))) (by positivity)
       _= _:=by ring

lemma log_payment (k:ℕ):∃ C:ℝ,0<C ∧ ∃ D:ℝ, 0≤D ∧ ∀ᶠ r in trail,
    ∀ s:ℝ, r ≤ s → s≤1 → (badge s*badge r)^k ≤ C*(g r)^(-D) := by
  let D:=G.slopeConstant⁻¹
  have hD:0<D:= inv_pos.mpr (Gauge.slopeConstant_pos hG)
  refine ⟨((2*D)^2)^k,by positivity,(↑(4*k:ℕ):ℝ),by positivity,?_⟩
  filter_upwards [strength_scale hG, strength_positive hG,to_log_zoom.eventually_ge_atTop 1,self_mem_nhdsWithin]
    with r hr hQ hz (hp:0<r) s hs h₁
  have hv:1≤run r:= by change 1≤ -Real.log r; change 1≤ Real.log r⁻¹ at hz; simpa [Real.log_inv] using hz
  have he:badge s ≤ badge r:=by unfold badge run; have:=Real.log_le_log hp hs; linarith
  have hb:0 ≤ badge r:=by unfold badge; linarith
  have ha:1 ≤ badge s:=le_add_of_nonneg_right (neg_nonneg.mpr (Real.log_nonpos (hp.le.trans hs) h₁))
  have hx: badge r≤2*D/(g r)^2:= by
     change Real.log r⁻¹*(g r)^2=D at hr
     have hU:=add_le_add_left hv (run r)
     change 1+run r≤_; rw [← hr, Real.log_inv]; rw [show 2*(-Real.log r*g r^2)/g r^2=2*run r by unfold run; field_simp]; linarith
  rw [Real.rpow_neg hQ.le,Real.rpow_natCast]
  calc _ ≤ (badge r*badge r)^k:= pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans ha) hb) (mul_le_mul_of_nonneg_right he hb) _
       _≤ ((2*D/(g r)^2)^2)^k:=by rw [← pow_two]; gcongr
       _= _:=by rw [pow_mul,← inv_pow]; ring

omit hG
lemma sameLength (v:Viewers F)(r T:ℝ)(o:E4)(x:Points n)(y:Points m)(u:Inputs G d)(w:Inputs G e):
    atLength F J v o r T x y u w=Fork.Yν F J d e v r (r*T) o x.ofLp y.ofLp u w := today_apply ..
lemma sameCenter (v:Viewers F)(r T:ℝ)(o:E4)(y:Points m)(w:Inputs G e)(hx:Injective (beside (sole o) (sites o (r*T) y))) :
    atCenter F J h v o r T y w = Fork.Dν F J e h v r (r*T) o y.ofLp w := by
  ext1 a; rw [center_length]; unfold atLength; rw [today_apply]; let e₁ : Fin 1 ≃ Unit := Equiv.ofUnique _ _
  let p : Labels S (fun _:Unit=>h):= sole (assign J r h a); let y' := sites o (r*T) y
  change whole (S:=S) (spectator F v) _ (labels J r (d:=Output h) _) y' _ = whole (spectator F v) (sole o) p y' _
  rw [show sites (n:=1) o r 0 = sole o ∘ e₁ from funext fun i=> by simp [sites,sole]]
  exact Orbits.whole_perm (w:=labels J (r*T) w) _ e₁ (Equiv.refl _) (v:=p) (spectate F v) hx

/-- G6 prices, continuum none and all selected viewers. Holds for any elected inputs as here, for every receding M interval
(little-o hypotheses on its clock not a hypothesis to derive this). Price on c_W; converts back to physical comparisons.
See `Ambient` and `Orbits.packet_read`. -/
def G6 (U B D : ℝ)(K:Set (Points n))(S':Set (Points m)):Prop:=
    ∃ b:ℝ,0≤b ∧ ∃ T₀≥(2:ℝ), ∀ᶠ r in trail,∀ T:ℝ,T₀≤T→ T≤U*(g r)^(-B)→
    ∀ x∈K,∀ y∈S',∀ o:E4,∀ (ω:Viewers F) (u: Inputs G d)(v:Inputs G e), Box u 1 → Box v 1 →
    let D' := fun p=>atCenter F J h p o r T y v
    let Y := fun p=>atLength F J p o r T x y u v
    let c := packet F J R h o r x u
    let b := b*(g r)^(-D)
    ‖Y ω-D' ω c‖ ≤ b * (r*T+(T^(h+1))⁻¹) ∧ ‖Y ω‖+width c+rowPrice (D' ω) ≤ b ∧
      ‖Y ω-Y none‖ + rowPrice (D' ω-D' none) ≤ b*(r*T)
lemma G6.target {K:Set (Points n)} {S':Set (Points m)} {U B D:ℝ} (H : G6 F R J d e h U B D K S') : PhysicalPacket F J R d e h U B D K S':= by
   obtain ⟨b,hb,r,hr,H⟩ := H; exact ⟨b,hb,r,hr,H.mono fun r hr T hx ht x h₁ y h₂ o v u w hu hv=> (hr T hx ht x h₁ y h₂ o v u w hu hv).1⟩

variable (K:Set (Points n))(S':Set (Points m))(hK:IsCompact K)(hx:K⊆conf n)(hS:IsCompact S')(hy:S'⊆Outside m)
include hK hx hS hy hG
theorem G6_forecast (Ht:LogTrace F R.port)(Hh:Coat F R J h)(HA:∀ i,Coat F R J (d i))(HB:∀ i,Coat F R J (e i)):
    ∃ D:ℝ,0≤D ∧ ∀ U B:ℝ,G6 F R J d e h U B D K S' := by
  obtain ⟨M,δ,hM,hδ,H⟩:= setup hK hx hS hy
  obtain ⟨C,hC,k,H'⟩:= Fork.log6 F R J d e h hM hδ hG Ht HA HB Hh
  obtain ⟨C',hc',D,hD,hk⟩:= log_payment hG k
  refine ⟨D,hD, fun U B=> ⟨C*C',by positivity,max (2:ℝ) (M/δ),le_max_left ..,?_⟩⟩
  filter_upwards [out_radius hG (U:=U) (B:=B) _ (H'.and ((ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)),
    hk,self_mem_nhdsWithin] with r hA hp (hr:0<r) T hT h0 x hxx y hyy o v u w hu hv
  have hT₀ : 1 ≤ T := le_trans (show (1:ℝ) ≤ 2 by norm_num) ((le_max_left ..).trans hT)
  obtain ⟨hA',hst⟩:= hA T hT₀ h0; let s:=r*T; have hs:r ≤ s:= le_mul_of_one_le_right hr.le hT₀
  let b:=C*C'*(g r)^(-D); have Hb: C*(OPE.Log.badge s*OPE.Log.badge r)^k ≤ b:=by
    exact (mul_le_mul_of_nonneg_left (hp _ hs hst) hC.le).trans_eq (by ring)
  have hx' := H x hxx y hyy
  have hgear:r*M ≤ s*δ:= by
    unfold s; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hδ).mp ((le_max_right ..).trans hT)) hr.le
  have he := (boxes zero_le_one).mp hu; have hv' := (boxes zero_le_one).mp hv; have ht := hr.trans_le hs
  obtain ⟨hx,hy,hz⟩:= hA' r o x.ofLp y.ofLp hr hs hx' hgear v u w he hv'
  have hx'' : Injective (beside (sole o) (sites o (r*T) y)):= Fork.center_layout o ht hδ hx'.away hx'.zclear
  specialize hp _ hs hst
  dsimp only; rw [sameLength F J d e v,sameLength F J d e none,sameCenter F J e h v _ _ _ _ w hx'', sameCenter F J e h none _ _ _ _ w hx'']
  have hP : s+(r/s)^(h+1) = r*T+(T^(h+1))⁻¹ := by unfold s; rw [show r/(r*T)= T⁻¹ from by field_simp, inv_pow]
  refine ⟨hx.trans ((mul_le_mul_of_nonneg_right Hb (add_nonneg ht.le (pow_nonneg (div_nonneg hr.le ht.le) _))).trans_eq
    (congrArg (b*·) hP)),hy.trans Hb,hz.trans (mul_le_mul_of_nonneg_right Hb ht.le)⟩
end YM.Integration.GradedFar
