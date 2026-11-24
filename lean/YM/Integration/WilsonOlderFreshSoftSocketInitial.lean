import YM.Integration.WilsonOlderFreshSoftSocketPlacement
import YM.Integration.WilsonOriginalPublicNodalStencils

/-! The full appointed physical basis tensor equals its original K-dosed socket tensor, before any conditional hearing. The real and imaginary readings, the unit and every cover share the same opening. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketInitial
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonReceivedCanonicalVerseBasis (dose restored basis)
open WilsonOriginalStarSceneWords (pole)
open WilsonMeasuredPointBareWords (Term)
open private atom from YM.Integration.IndependentSourcePathFamily
open WilsonPositionProgramBlockedTrialAddBack WilsonCoeffUV.Winding RegulatorIR.FVAAlt2
open ActualRunPhysicalPages Pert.Asymptotics
variable {G:Gauge}{I:Type}[DecidableEq I](R:Run G)(d:I→ℕ)(b:Columns R d)
  {D:I→ℕ}(κ:(i:I)→Knob (D i))(pt:I→Chamber){N per K:ℕ}
local notation "g" => regulatorRun R.family N per K
local notation "P_" => WilsonOlderFreshSoftFigures.seed R D d b κ pt
def charge (N per K:ℕ)(i:I)(c:Choice R d i):ℂ:=
  dose R d N per K (request R d b (N:=N) (p:=per) (K:=K)) i c*
    ((regulatorRun R.family N per K:ℝ):ℂ)^(-(pole R d (entry R d i c):ℤ))

private theorem evaluated (L:ℂ→L[ℝ]ℝ)(w:ℂ)(a:ℝ):L (w*(a:ℂ))=L w*a:=by
  rw [mul_comm w,←Complex.real_smul,L.map_smul,smul_eq_mul,mul_comm]

omit [DecidableEq I] in
private theorem realAt (i:I)(n:Side)(oo:Site n)(U:Config G n):
    (((R.family.localSection (d i)).places (Pi.single (b i) 1) oo U).re:ℂ)=
      (R.family.localSection (d i)).places (Pi.single (b i) 1) oo U:=by
  apply Complex.conj_eq_iff_re.mp
  let v:=(Pi.single (b i) 1:(R.family.labels.level (d i)).Coeff)
  have hreal:=(R.makes.sections (d i)).ordinary_real v (expandAt oo U)
  change (R.family.localSection (d i)).evaluate (star v) _=star ((R.family.localSection (d i)).evaluate v _) at hreal
  change star ((R.family.localSection (d i)).evaluate v _)=_
  rw [←hreal]
  have bar:star v=v:=by funext k;simp [v,Pi.single_apply]
  rw [bar];rfl

omit [DecidableEq I] in
private theorem issued (live:K≤N)(L:ℂ→L[ℝ]ℝ)(i:I)(n:Side)(U:Config G n):
    (∑m:Term R (d i) (b i),L 1*(atom (P_ i m)).unmasked U 0)=
      ∑c:Choice R d i,L (charge R d b N per K i c)*(atom (WilsonReceivedCanonicalVerseBasis.basis R d κ pt i c)).unmasked U 0:=by
  classical
  rw [←Finset.mul_sum,←WilsonOlderFreshSoftFigures.field R D d]
  have sampled:=WilsonOriginalPublicNodalStencils.letter R d b (p:=per) live κ pt i (0:Site n) U
  have real:=realAt R d b i n 0 U
  have left:(L 1)*((R.family.localSection (d i)).places (Pi.single (b i) 1) 0 U).re=
      L ((R.family.localSection (d i)).places (Pi.single (b i) 1) 0 U):=by
    conv_rhs => rw [←real]
    simpa only [one_mul] using (evaluated L 1 _).symm
  rw [left,sampled,map_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold restored charge
  rw [←mul_assoc,evaluated]
  rfl

theorem original (live:K≤N)(L:ℂ→L[ℝ]ℝ)(i:I)(z:Cover):
    L 1 • IndependentSourcePathFamily.single P_ i z=
      ∑c:Choice R d i,L (charge R d b N per K i c) • WilsonOlderFreshSoftSocketGeometry.row R d κ pt i c z:=by
  classical
  unfold IndependentSourcePathFamily.single
  rw [Finset.smul_sum]
  exact WilsonOlderFreshSoftSocketPlacement.original D i (κ i) (pt i) z
    (M:=Term R (d i) (b i)) (N:=Choice R d i)
    (fun m=>atom (P_ i m)) (fun c=>atom (WilsonReceivedCanonicalVerseBasis.basis R d κ pt i c)) (fun _=>L 1)
    (fun c=>L (charge R d b N per K i c)) (fun _ u v=>OriginalMarkedSourceComet.invariant _ _ _ _ u v)
    (fun _ u v=>OriginalMarkedSourceComet.invariant _ _ _ _ u v) (issued R d b κ pt live L i)

end YM.Integration.WilsonOlderFreshSoftSocketInitial
end
