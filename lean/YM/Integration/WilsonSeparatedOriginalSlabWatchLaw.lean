import YM.Integration.WilsonSeparatedOriginalSlabWatchGrid

/-! Fixed-radius continuum return of the genuine emitted collective and the unshifted macroscopic detector on one original Wilson field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchLaw
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Records WilsonReportingUnitOrbit WilsonReportHarvestReadmittedSource WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabPhysicalStencil WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchGrid
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I][DecidableEq I]

omit [DecidableEq I] in
def price (C:Family G)(s:I→ℕ)(m:ℕ)(r:ℝ):ℂ:=(∏_i:I,(r:ℂ)⁻¹^4)*phase⁻¹^Fintype.card I*∏i,(C.S.a m:ℂ)^(s i)

omit [DecidableEq I] in
theorem paid (s:I→ℕ)(m N:ℕ)(r:ℝ):weight (C:=C) s m N r=price C s m r*(C.S.a N:ℂ)^(4*Fintype.card I):=by
  simp only [WilsonSeparatedOriginalSlabPhysicalBox.weight,WilsonSeparatedOriginalSlabPhysicalStencil.mesh,price,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←pow_mul];ring

def actual (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(k m:ℕ)(Ψ:Wave I)(g:Body)(p:ℕ×ℕ):ℂ:=
  if hn:k≤p.1 then moment (C.beta p.1 p.2) (fun V=>constellation s (fun i=>Many.point (Y p i) (filed L (s i) r (w i) (Y p i) m p.1 p.2) m p.1) r Ψ hn m g V*W.plot p.1 p.2 V) else 0

omit [DecidableEq I] in
def reading (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(k m:ℕ)(Ψ:Wave I)(g:Body):ℂ:=
  price C s m r * ∫x:Points (Fintype.card I),test C k r Ψ g x*signal L W s r w x

theorem tested (L:Layout F)(made:C.Makes)(E:Services C f S)(W:Watch C)(s:I→ℕ){l:Filter (ℕ×ℕ)}[l.NeBot](law:l≤f.fuse)(lens:l≤L.lens)
    (k m:ℕ){r cap:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(openRef:∀i,C.ref (s i)≤L.level r)(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(Ψ:Wave I)(g:Body)
    (A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(bounded:∀y∈A,∀i,‖y i‖≤cap)(sep:band W k r A⊆conf _):
    Tendsto (actual L W s r w Y k m Ψ g) l (𝓝 (reading L W s r w k m Ψ g)):=by
  apply ((observed L W s E law lens k rp w openRef Ψ g A hA enc sep).const_mul (price C s m r)).congr'
  have level:=((OPE.Cards.largeMesh f).eventually_ge_atTop (max k m)).filter_mono law
  have volume:=((C.S.radius_diverges.comp (WilsonSeparatedOriginalSlabWatchPlacement.periods f)).eventually_gt_atTop (r*cap+2*C.S.a k)).filter_mono law
  filter_upwards [level,volume] with p height room
  have hk:k≤p.1:=(le_max_left _ _).trans height
  have hm:m≤p.1:=(le_max_right _ _).trans height
  rw [actual,dif_pos hk,WilsonSeparatedOriginalSlabWatchedCensus.issued L made W s r w (Y p) m hm Ψ hk rp (fun y hy=>bounded y (enc hy)) room g]
  rw [←mul_assoc,←paid,Finset.mul_sum]
  apply Finset.sum_congr (by ext x;simp only [Finset.mem_univ]);intro x _;simp only [book,mul_assoc]


theorem original (L:Layout F)(made:C.Makes)(E:Services C f S)(W:Watch C)(s:I→ℕ)
    (k m:ℕ){r cap:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(openRef:∀i,C.ref (s i)≤L.level r)(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(Ψ:Wave I)(g:Body)
    (A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(bounded:∀y∈A,∀i,‖y i‖≤cap)(sep:band W k r A⊆conf _):
    Tendsto (actual L W s r w Y k m Ψ g) L.lens (𝓝 (reading L W s r w k m Ψ g)):=by
  letI:=L.notbot
  exact tested L made E W s L.certified le_rfl k m rp w openRef Y Ψ g A hA enc bounded sep

end YM.Integration.WilsonSeparatedOriginalSlabWatchLaw
