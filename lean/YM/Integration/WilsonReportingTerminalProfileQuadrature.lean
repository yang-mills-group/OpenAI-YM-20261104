import YM.Integration.WilsonReportingTerminalPrimaryCensus

/-! The price of the authentic position-test cohort before the period and
cutoff. Its positive weight per leg is the true microscopic cell volume. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalProfileQuadrature
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG05Readout
open Native Pulse PhysicalNext.Repeat.Legato
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (C:Family G) {I:Type} [Fintype I] {b N per:ℕ}

def weight (s:I→ℕ) (m N:ℕ) (r:ℝ):ℂ:=∏i,((r:ℂ)⁻¹^4*(C.S.a m:ℂ)^(s i)*(C.S.a N:ℂ)^4)
def areaWeight (s:I→ℕ) (m b:ℕ) (r:ℝ):ℝ:=∏i,(r⁻¹^4*C.S.a m^(s i)*C.S.a b^4)

private theorem count (s:I→ℕ) (r:ℝ) (rp:0<r) (m:ℕ) (live:b≤N) :
    ‖weight C s m N r‖*(Fintype.card (I→Site (C.S.toDepth live per).count):ℝ)=areaWeight C s m b r := by
  let A:=C.S.toDepth live per
  rw [weight,norm_prod,Fintype.card_pi,Nat.cast_prod,← Finset.prod_mul_distrib]
  unfold areaWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [Lattice.site_card,Nat.cast_pow]
  simp only [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg rp.le,
    Real.norm_of_nonneg (C.S.a_pos _).le]
  rw [← C.S.embeds_scale A,mul_pow]
  ring

def bill (s:I→ℕ) (m b J:ℕ) (r:ℝ) (g:Body):ℝ:=
  areaWeight C s m b r*((Lattice.box J).card^(Fintype.card I):ℕ)*
    ∫ z in Native.box,‖g.val z‖

theorem original (s:I→ℕ) (m J:ℕ) (r:ℝ) (rp:0<r) (g:Body) (live:b≤N)
    (E:(I→Site (C.side b per))→(I→Site (C.S.toDepth live per).count)→E4→ℂ)
    {δ:ℝ} (dp:0≤δ) (entry:∀o∈area (C:=C) (p:=per) (b:=b) (V:=I) J,∀u,∀z∈Native.box,‖E o u z‖≤δ) :
    ‖weight C s m N r * ∑o∈area (C:=C) (p:=per) (b:=b) (V:=I) J,
       ∫z in Native.box,g.val z*∑u,E o u z‖≤bill C s m b J r g*δ := by
  let A:=C.S.toDepth live per
  let Z:=area (C:=C) (p:=per) (b:=b) (V:=I) J
  let n:ℝ:=Fintype.card (I→Site A.count)
  let p:ℝ:=∫ z in Native.box,‖g.val z‖
  have pp:0≤p:=integral_nonneg (fun _=>norm_nonneg _)
  have meas:IntegrableOn (fun z=>‖g.val z‖) Native.box:=by
    exact ((show ContDiff ℝ ∞ g.val from g.property).continuous.norm.continuousOn).integrableOn_compact Pert.Cellular.cells_compact
  have one (o) (good:o∈Z):‖∫z in Native.box,g.val z*∑u,E o u z‖≤p*(n*δ):=calc
    _ ≤ ∫ z in Native.box,‖g.val z*∑u,E o u z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in Native.box,‖g.val z‖*(n*δ):=by
      refine integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (meas.mul_const _) ?_
      apply ae_restrict_of_forall_mem Pert.Cellular.cells_compact.measurableSet
      intro z hz
      change ‖g.val z*∑u,E o u z‖≤‖g.val z‖*(n*δ)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le ..).trans
      calc ∑u,‖E o u z‖≤∑ _u:I→Site A.count,δ:=Finset.sum_le_sum (fun u _=>entry o good u z hz)
           _=n*δ:=by simp [n]
    _ = p*(n*δ):=integral_mul_const ..
  have major:((Z.card:ℕ):ℝ)≤((Lattice.box J).card^(Fintype.card I):ℕ):=by
    exact_mod_cast (area_cost (C:=C) (p:=per) (b:=b) (V:=I) J)
  have n0:0≤n:=Nat.cast_nonneg _
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)).trans
  calc
    _ ≤ ‖weight C s m N r‖ * (∑ _o∈Z,p*(n*δ)):=mul_le_mul_of_nonneg_left (Finset.sum_le_sum one) (norm_nonneg _)
    _ = (‖weight C s m N r‖*n)*(Z.card:ℝ)*p*δ:=by rw [Finset.sum_const,nsmul_eq_mul];ring
    _ ≤ (‖weight C s m N r‖*n)*((Lattice.box J).card^Fintype.card I:ℕ)*p*δ:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left major (mul_nonneg (norm_nonneg _) n0)) pp) dp
    _ = bill C s m b J r g*δ:=by rw [show ‖weight C s m N r‖*n=areaWeight C s m b r from count C s r rp m live];rfl

end YM.Integration.WilsonReportingTerminalProfileQuadrature
