import YM.Integration.WilsonThermometerWeakMovingCorner
import YM.OPE.Log.Measuring

/-! Scale-weighted physical coordinates on the original common filtered
Wilson law.  Both the thermal lift and the filtered output use the same
numerical cutoff sequence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRunningCoordinates
open Filter Set Function Spec Table Climb Extraction Trace Trace.Pilot Trace.Terrace
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 OPE OPE.Log
open PhysicalNext.Repeat.Legato Next.UVStress
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem assessed {𝓛:Ultrafilter (ℕ×ℕ)}(ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    {d w:ℕ}(L:S.Field d→ₗ[ℂ]ℂ)(h:w≤d)
    (kill:∀e:ℕ,∀he:e<w,∀v:S.Field e,L (F.sector.derivatives.rise (he.le.trans h) v)=0):
    ∃p:ℕ,∀ᶠ j in atTop,∀(r A:ℝ)(m:ℕ),Turnkey F 𝓛 r j m d A→∀v:S.Field d,
      ‖L v‖≤(R.family.path.levels.clock.hatBeta j)^p*(R.family.S.a j)^w*A*cost F d r v:=by
  obtain ⟨p,H⟩:=ledger.outlet d w L h kill
  refine ⟨p,H.mono ?_⟩
  intro j hj r A m key v
  obtain ⟨Z,Y,pr,tends,paid⟩:=key.coin v
  have lin:= hj (𝓛:Filter _) le_rfl Y Z _ (paid.mono fun x hx=>hx.1) tends
  rw [pr] at lin
  have split:(R.family.S.a j)^d=(R.family.S.a j)^(d-w)*(R.family.S.a j)^w:=by
    rw [←pow_add,Nat.sub_add_cancel h]
  calc _≤_:=lin
       _=_:=by rw [split]; field_simp [(R.family.S.a_pos j).ne']

private lemma clock {simple:G.Simple}{𝓛:Ultrafilter (ℕ×ℕ)}{j m d t:ℕ}{r:ℝ}
    (K:Pool F 𝓛 r j m d (dock r^t))(hr:r∈Ioc (0:ℝ) 1):
    R.family.path.levels.clock.hatBeta j ≤
      (R.family.path.levels.clock.bar+G.slopeConstant*((t:ℝ)+1))*dock r:=by
  let a:=R.family.S.a j
  have da:1≤dock r:=dock_valid r hr
  have pos:0<dock r:=zero_lt_one.trans_le da
  have gap:=Real.log_lt_log hr.1 K.breadth
  rw [Real.log_mul (pow_pos pos _).ne' (R.family.S.a_pos j).ne',Real.log_pow] at gap
  have paid:(R.family.S.scale j) ≤ ((t:ℝ)+1)*dock r:=by
    change Real.log (R.family.S.a j)⁻¹ ≤ _
    rw [Real.log_inv]
    have slope:Real.log (dock r)≤dock r:=Real.log_le_self pos.le
    have rd: -Real.log r≤dock r:=by unfold dock LogV; rw [Real.log_inv]; linarith
    linarith [mul_le_mul_of_nonneg_left slope (Nat.cast_nonneg t)]
  change R.family.path.levels.clock.bar+G.slopeConstant*R.family.S.scale j≤_
  have rate:=mul_le_mul_of_nonneg_left paid (Gauge.slopeConstant_pos (G:=G) simple).le
  nlinarith only [rate,le_mul_of_one_le_right R.family.path.levels.clock.bar_pos.le da]

theorem original {simple:G.Simple}{A:EveryPhase.Almanac F}(H:Roll.{u} F simple A)
    (agency:∀𝓛:Ultrafilter (ℕ×ℕ),(𝓛:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    {d w:ℕ}(L:S.Field d→ₗ[ℂ]ℂ)(h:w≤d)
    (kill:∀e:ℕ,∀he:e<w,∀v:S.Field e,L (F.sector.derivatives.rise (he.le.trans h) v)=0):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠr in trail,∀v:S.Field d,
      ‖L v‖≤C*dock r^m*r^w*cost F d r v:=by
  obtain ⟨H₀,Z,𝓛,_,_,_,_,_,_,bliss,_⟩:=H.commonFrame
  obtain ⟨p,priced⟩:=assessed F (agency 𝓛 bliss.lies) L h kill
  obtain ⟨t,opened⟩:=every_pool F simple bliss d
  obtain ⟨j₀,hj⟩:=eventually_atTop.1 priced
  let C:=R.family.path.levels.clock.bar+G.slopeConstant*((t:ℝ)+1)
  have cp:0≤C:=add_nonneg R.family.path.levels.clock.bar_pos.le
    (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le (by positivity))
  refine ⟨C^p,p+t*w+t,pow_nonneg cp _,?_⟩
  have slope:∀ᶠr in trail,r*(dock r)^t≤R.family.S.a j₀:=(lake_line t).eventually (ge_mem_nhds (R.family.S.a_pos j₀))
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [opened,slope,small,self_mem_nhdsWithin] with r hire paid small pos
  intro v
  obtain ⟨j,m,key⟩:=hire
  have sp:R.family.S.a j≤r*dock r^t:=(R.family.S.strictAnti.antitone key.fore).trans key.front.le
  have next:j₀≤j:=R.family.S.strictAnti.le_iff_ge.mp (sp.trans paid)
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  have aj:R.family.S.a j≤1:=by simpa using R.family.S.strictAnti.antitone (Nat.zero_le j)
  have sj:0≤R.family.S.scale j:=by change 0≤Real.log (R.family.S.a j)⁻¹; rw [Real.log_inv]; linarith [Real.log_nonpos (R.family.S.a_pos j).le aj]
  have hat:0≤R.family.path.levels.clock.hatBeta j:=add_nonneg R.family.path.levels.clock.bar_pos.le (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le sj)
  have β:=pow_le_pow_left₀ hat (clock F (simple:=simple) key ⟨pos,small⟩) p
  have width:=pow_le_pow_left₀ (R.family.S.a_pos j).le sp w
  have marked:= hj j next r _ m (key.budget d le_rfl) v
  calc ‖L v‖≤_:= marked
       _≤(C*dock r)^p*(r*dock r^t)^w*dock r^t*cost F d r v:=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul β width (pow_nonneg (R.family.S.a_pos j).le _) (pow_nonneg (mul_nonneg cp dk) _))
            (pow_nonneg dk _)) (Real.sqrt_nonneg _)
       _=_:=by rw [mul_pow,mul_pow,←pow_mul,pow_add,pow_add];ring

end YM.Integration.WilsonThermometerWeakRunningCoordinates
end
