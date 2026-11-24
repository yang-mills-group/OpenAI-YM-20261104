import YM.Integration.WilsonMeasuredSignedActionOriginalTables
import YM.Integration.WilsonViewerElectedHierarchy

/-! The selected position frame and the issued Wilson table read the same
directed trace line. Scalar subtraction is performed only after the full
one-point functional has acted. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionPosition
open Function Filter Set Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open WilsonMeasuredSignedActionOriginalTables WilsonThermometerUnitFilingFourSquare
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)

private theorem projected : centering S 4 (center F)=lum F:=by
  let d:=stressTrace F.sector.energy
  let q:=euclideanVEV S S d-euclideanVEV S (selected F) d
  have same:center F=lum F+q • S.unit 4:=by
    change d-_=d-_+_;unfold q;rw[sub_smul];abel
  rw [same,map_add,map_smul,const_out F.room.kernel.laws,smul_zero,add_zero]
  exact zero_center (⟨_,lum_active F⟩:Active S)

theorem positioned (simple:G.Simple){J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (filed:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g):
    ∀ᶠ r in trail,Ray F (J r 4 (stepField C)):=by
  obtain ⟨c,stamp⟩:=cal.centered
  have small: -b0 G/2 < 0:=by rw [←force_b];exact force_neg simple
  filter_upwards [filed,stamp,(cal.measures g heat).eventually (gt_mem_nhds small),heat.positive,
    (self_mem_nhdsWithin:∀ᶠ r in trail,r∈Ioi (0:ℝ))] with r same h price pos rpos
  have neg:δ r<0:=(div_lt_iff₀ (sq_pos_of_pos pos)).mp price |>.trans_eq (zero_mul _)
  change 0<r at rpos
  rw [same]
  have paid:=congrArg ((centering S 4).restrictScalars ℝ) h
  change (centering S 4) (r^4 • center F)=
    (centering S 4) ((4*δ r) • (P r (stepField C))+ r^4 • (c • S.unit 4)) at paid
  have scale (n:ℝ)(a:S.Field 4): centering S 4 (n • a)=n • centering S 4 a:=
    ((centering S 4).restrictScalars ℝ).map_smul n a
  rw [scale,projected F,map_add,scale,scale,map_smul,const_out F.room.kernel.laws,smul_zero,smul_zero,add_zero] at paid
  refine ⟨-(4*δ r)/r^4,div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (by norm_num) neg)) (pow_pos rpos _),?_⟩
  calc
    _ = (-(r^4)⁻¹) • ((4*δ r) • centering S 4 (P r (stepField C))) := by
      rw [smul_smul];congr 1;ring
    _ = -lum F :=by rw [←paid,smul_smul];simp [rpos.ne']

theorem sameRay {W:Spin.change S 4} {y:S.Field 4}
    (unit:W ((Bel C.book).unit 4)=S.unit 4) (old:Ray F (W (stepField C))) (phys:Ray F y):
    ∃ (a:ℝ) (b:ℂ),0<a ∧ W.symm y=a • stepField C + b • (Bel C.book).unit 4:=by
  obtain ⟨s,sp,hs⟩:=old
  obtain ⟨t,tp,ht⟩:=phys
  have eq:centering S 4 y=(s/t) • centering S 4 (W (stepField C)):=by
    apply smul_right_injective _ tp.ne'
    change t • centering S 4 y=t • ((s/t) • centering S 4 (W (stepField C)))
    rw [ht,←hs,smul_smul]
    congr 1;field_simp
  let b:=expectation S 4 y-(s/t:ℝ) • expectation S 4 (W (stepField C))
  refine ⟨s/t,b,div_pos sp tp,?_⟩
  apply W.injective
  rw [W.apply_symm_apply,map_add,show W ((s/t) • stepField C)=(s/t) • W (stepField C) from (W.toLinearMap.restrictScalars ℝ).map_smul ..,map_smul,unit]
  rw [value_center,value_center,smul_sub] at eq
  unfold b
  rw [sub_smul,smul_assoc]
  calc
    y = (y-expectation S 4 y • S.unit 4)+expectation S 4 y • S.unit 4:=by abel
    _ = _ :=by rw [eq];abel

end YM.Integration.WilsonMeasuredSignedActionPosition
