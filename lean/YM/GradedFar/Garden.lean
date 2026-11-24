import YM.GradedFar.Horizon
/-!
# G6 also if choosing **T≥1** directly with the fork hypothesis

Instead of first demanding T sufficiently large, still require the original
`r M ≤ s δ`. Then even witness of the budget C works for all Λ,B (threshold radius depends).
Exercise with Vote using `Batch.Q2`.
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
-- point-ready version on ALL two-zone geometry with that fork certificate

theorem G6_twoZone (hG:G.Simple)(M δ:ℝ)(hM:0≤M)(hδ:0<δ)(Ht:LogTrace F R.port)(Hh:Coat F R J h)(HA:∀ i,Coat F R J (d i))(HB:∀ i,Coat F R J (e i)):
    ∃ D:ℝ,0≤D ∧ ∃ b:ℝ, 0≤b ∧ ∀ U B:ℝ,∀ᶠ r in trail,∀ T:ℝ,1≤T→ T≤U*(g r)^(-B)→ r*M≤ r*T*δ →
        ∀ (x:Points n)(y:Points m), Setting M δ x.ofLp y.ofLp →
        ∀ (o:E4)(ω:Viewers F) (u: AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1 → Box v 1 →
        let D' := fun p=>atCenter F J h p o r T y v
        let Y := fun p=>atLength F J p o r T x y u v
        let c := packet F J R h o r x u
        let b := b*(g r)^(-D)
        ‖Y ω-D' ω c‖ ≤ b * (r*T+(T^(h+1))⁻¹) ∧ ‖Y ω‖+width c+rowPrice (D' ω) ≤ b ∧
          ‖Y ω-Y none‖ + rowPrice (D' ω-D' none) ≤ b*(r*T) := by
  obtain ⟨C,hC,k,H'⟩:= Fork.log6 F R J d e h hM hδ hG Ht HA HB Hh
  obtain ⟨C',hc',D,hD,hk⟩:= log_payment hG k
  refine ⟨D,hD,C*C',by positivity,fun U B=>?_⟩
  filter_upwards [out_radius hG (U:=U) (B:=B) _ (H'.and ((ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)),
    hk,self_mem_nhdsWithin] with r hA hp (hr:0<r) T hT₀ h0 hgear x y hx' o v u w hu hv
  obtain ⟨hA',hst⟩:= hA T hT₀ h0; let s:=r*T; have hs:r ≤ s:= le_mul_of_one_le_right hr.le hT₀
  let b:=C*C'*(g r)^(-D); have Hb: C*(OPE.Log.badge s*OPE.Log.badge r)^k ≤ b:=by
    exact (mul_le_mul_of_nonneg_left (hp _ hs hst) hC.le).trans_eq (by ring)
  have he := (boxes zero_le_one).mp hu; have hv' := (boxes zero_le_one).mp hv; have ht := hr.trans_le hs
  obtain ⟨hx,hy,hz⟩:= hA' r o x.ofLp y.ofLp hr hs hx' hgear v u w he hv'
  have hx'' : Injective (beside (sole o) (sites o (r*T) y)):= Fork.center_layout o ht hδ hx'.away hx'.zclear
  specialize hp _ hs hst
  dsimp only; rw [sameLength F J d e v,sameLength F J d e none,sameCenter F J e h v _ _ _ _ w hx'', sameCenter F J e h none _ _ _ _ w hx'']
  have hP : s+(r/s)^(h+1) = r*T+(T^(h+1))⁻¹ := by unfold s; rw [show r/(r*T)= T⁻¹ from by field_simp, inv_pow]
  refine ⟨hx.trans ((mul_le_mul_of_nonneg_right Hb (add_nonneg ht.le (pow_nonneg (div_nonneg hr.le ht.le) _))).trans_eq
    (congrArg (b*·) hP)),hy.trans Hb,hz.trans (mul_le_mul_of_nonneg_right Hb ht.le)⟩
end YM.Integration.GradedFar
