import YM.Integration.WilsonSeparatedOriginalSlabWatchFubini
import YM.Integration.WilsonSeparatedOriginalSlabWatchContrast

/-! Physical radius, engineering factors and the original shared centre after the exact affine change of all spatial variables. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchNormalization
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse WilsonReportingUnitOrbit WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchFubini WilsonSeparatedOriginalSlabWatchLaw
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

def factor (C:Family G)(s:I→ℕ)(m:ℕ):ℂ:=phase⁻¹^Fintype.card I*∏i,(C.S.a m:ℂ)^(s i)

theorem currency (s:I→ℕ)(m:ℕ)(r:ℝ):price C s m r=factor C s m*((r:ℂ)^(4*Fintype.card I))⁻¹:=by
  simp only [price,factor,Finset.prod_const,Finset.card_univ,←pow_mul,inv_pow];ring

theorem affine (k:ℕ){r:ℝ}(rp:0<r)(z:E4)(H:Points (Fintype.card I)→ℂ):
    ((r:ℂ)^(4*Fintype.card I))⁻¹*(∫x,H x)=∫y,H (positions (I:=I) C k r z y):=by
  let P (x:Points (Fintype.card I)):=H (x+WilsonSeparatedOriginalSlabWatchFubini.point (I:=I) C k z)
  have trans:(∫x,P x)=∫x,H x:=integral_add_right_eq_self H (WilsonSeparatedOriginalSlabWatchFubini.point (I:=I) C k z)
  have scale:=Measure.integral_comp_smul_of_nonneg volume P r (hR:=rp.le)
  rw [Next.UVStress.point_dimension,Complex.real_smul,trans] at scale
  simpa only [P,WilsonSeparatedOriginalSlabWatchFubini.positions,Complex.ofReal_inv,Complex.ofReal_pow] using scale.symm

theorem source (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(H:Points (Fintype.card I)→ℂ)(hc:ContinuousOn H (footprint C k r A)):
    ((r:ℂ)^(4*Fintype.card I))⁻¹*(∫x,test C k r Ψ g x*H x)=∫z in Native.box,g.val z*(∫y,Ψ.val (native y)*H (positions (I:=I) C k r z y)):=by
  rw [exchanged k rp Ψ g A hA enc H hc,←integral_const_mul]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z _
  change ((r:ℂ)^(4*Fintype.card I))⁻¹*(∫x,sheet C k r Ψ g (native x) z*H x)=_
  rw [affine (C:=C) (I:=I) k rp z (fun x=>sheet C k r Ψ g (native x) z*H x)]
  change _=g.val z*(∫y,Ψ.val (native y)*H (positions (I:=I) C k r z y))
  rw [←integral_const_mul];apply integral_congr_ae;apply Eventually.of_forall;intro y
  dsimp only;rw [physical rp];ring

def positionsReading (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(k m:ℕ)(Ψ:Wave I)(g:Body):ℂ:=
  factor C s m*∫z in Native.box,g.val z*(∫y,Ψ.val (native y)*signal L W s r w (positions (I:=I) C k r z y))

theorem normalized (L:Layout F)(W:Watch C)(s:I→ℕ){r:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(k m:ℕ)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    reading L W s r w k m Ψ g=positionsReading L W s r w k m Ψ g:=by
  rw [WilsonSeparatedOriginalSlabWatchLaw.reading,currency,mul_assoc,source k rp Ψ g A hA enc _ (licensed L W s k r w A sep)];rfl

end YM.Integration.WilsonSeparatedOriginalSlabWatchNormalization
