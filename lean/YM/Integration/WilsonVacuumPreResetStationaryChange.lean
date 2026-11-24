import YM.Integration.OriginalMarkedHeatCovariance
import YM.Integration.OriginalTwoChartMarkedWick
import YM.Integration.PhysicalForestCenter
import YM.Integration.OriginalIndependentForestLog
import YM.Integration.WilsonVacuumPreResetTorusUpperQuadratic

/-! Change from the absolute fine links to the measured relative coordinates for any quiet inlet with the original quadratic part. The finite-side cover inlet is tested on the very same stationary branch. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetStationaryChange
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G : Gauge} (R : Run G) (N m p : ℕ) (hm : m < N)
abbrev levels := R.family.path.levels
abbrev step := (levels R).clock.op m p
abbrev fine := (levels R).S.side (m+1) p
abbrev coarse := (levels R).S.side m p
abbrev ratio := R.metals.O
abbrev model := (RunFormalChain.fromRun R).step N m p hm
abbrev upper := freeForms (levels R) N (m+1)
abbrev lower := freeForms (levels R) N m
abbrev prediction := Bloch.installed (step R m p).ratio (predictionA (levels R) N m)

variable (F : Forest (step R m p).ratio) (tag : (step R m p).Choices)
abbrev saddle := extractV G (step R m p) F (prediction R N m p)
abbrev slice := camSlice G (step R m p) F (saddle R N m p F)
abbrev center := fderiv ℝ ((model R N m p hm).b F) 0
abbrev shift := shore (step R m p) F (saddle R N m p F) (center R N m p hm F)
abbrev precision := treeMatrix G (step R m p) F (upper R N m)
abbrev haar := loom (slice R N m p F) (jet (unhaar (n:=(fine R m p)) (ratio R)))
abbrev coarseAction := holdUp (Active G F) (orbC (precisionC G (coarse R m p) (lower R N m)))
abbrev relativeHaar := jet (stampJ (step R m p) F (center R N m p hm F) (ratio R))
variable (prior:PChart G (fine R m p)) (shell:shellK 2 prior)
variable (head:prior 0=shine (orbQ (precisionC G (fine R m p) (upper R N m))))

include tag in
/-- A genuinely centered change of the free variables over the unchanged
coarse spectator, with identity full first-order part. -/
theorem leading (j : Active G F) : constantCoeff (spool (shift R N m p hm F) j) =
    constantCoeff (noiseLine (Y:=Woods G (coarse R m p)) (1 : Matrix (Active G F) (Active G F) ℝ) j) :=
  PhysicalForestCenter.grade_zero (step R m p) F (saddle R N m p F) (model R N m p hm)
    (OriginalMarkedHeatCovariance.stationary R N m p hm F tag) j

include hm tag in
private theorem invertible : IsUnit (precision R N m p F).det := by
  have pos := (model R N m p hm).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N m p hm F tag] at pos
  exact isUnit_iff_ne_zero.mpr pos.det_pos.ne'

private theorem genuine_cov : (model R N m p hm).covariance F tag = (precision R N m p F)⁻¹ := by
  unfold Bulk.Kernel.covariance
  rw [OriginalMarkedHeatCovariance.precision R N m p hm F tag]

include hm in
private theorem auxiliary : Inputs (step R m p) (prediction R N m p) ((upper R N m).acts (fine R m p)) ((lower R N m).acts (coarse R m p)) :=
  horizon_step (levels R) m N hm _ _ (step R m p).sizes

include tag in
private theorem area : (motionJ (spool (shift R N m p hm F))).det * raiseE (retool (shift R N m p hm F) (haar R N m p F)) = raiseE (relativeHaar R N m p hm F) := by
  let a := stampJ (step R m p) F (center R N m p hm F) (ratio R)
  let l (u : Sloc (step R m p) F G) := unhaar (ratio R) ((slice R N m p F)*ᵥu)
  have ha : Green a := stamp_d (step R m p) F (center R N m p hm F) (ratio R) R.alloy.B.ratio (center R N m p hm F).contDiff.contDiffAt (map_zero _)
  have haz : a 0 = 0 := stamp_o (step R m p) F (center R N m p hm F) (ratio R) R.alloy.B.ratio (map_zero _)
  have hl : Green l := (show ContDiffAt ℝ ω (unhaar (n:=(fine R m p)) (ratio R)) ((slice R N m p F)*ᵥ0) by
    rw [Matrix.mulVec_zero]; exact unhaar_green R.alloy.B.ratio).comp 0 (board (slice R N m p F))
  have hlz : l 0 = 0 := by dsimp [l]; rw [Matrix.mulVec_zero,unhaar_zero R.alloy.B.ratio]
  have ht := shore_green (step R m p) F (saddle R N m p F) (center R N m p hm F) (center R N m p hm F).contDiff.contDiffAt (map_zero _)
  have hz := shore_zero (step R m p) F (saddle R N m p F) (center R N m p hm F) (map_zero _)
  have vold := sweeps G (step R m p) F (prediction R N m p) (lower R N m) (invertible R N m p hm F tag) (auxiliary R N m p hm)
  have transport := shape_area (step R m p) F (saddle R N m p F) (center R N m p hm F) (ratio R) (center R N m p hm F).contDiff.contDiffAt
    (map_zero _) R.alloy.B.ratio vold
  have hy := spider_green ht
  have ho := spider_zero hz
  let d (x : Sloc (step R m p) F G) := (edgeM (shift R N m p hm F) x).det
  have hcomp : Green (l ∘ spider (shift R N m p hm F)) :=
    (show ContDiffAt ℝ ω l (spider (shift R N m p hm F) 0) from ho.symm ▸ hl).comp 0 hy
  have tariff : (haar R N m p F) = jet l := loom_jet (slice R N m p F) _ (unhaar_green R.alloy.B.ratio)
  rw [tariff,← solar_motion (shift R N m p hm F) ht hz,pivot,traveling (spider (shift R N m p hm F)) hy ho l hl,
    ← literal_exp ha haz, ← literal_exp hcomp ((congrArg l ho).trans hlz),
    ← jet_mul (f:=d) (by apply MGreen.det; exact edge_green (shift R N m p hm F) ht)
      (g:=fun x => Real.exp ((l ∘ spider (shift R N m p hm F)) x)) hcomp.exp]
  exact jet_congr transport

/-- Relative log-density for the actual RG02 covariance. `b` accounts for
the common change of the zero-source scalar. -/
def relativePhase (b : Ink (Woods G (coarse R m p))) :=
  (relativeHaar R N m p hm F) - (retool (shift R N m p hm F) (unscaled (step R m p) F (prediction R N m p) prior - (coarseAction R N m p F)) + holdUp (Active G F) b) +
    bodyQ (Woods G (coarse R m p)) (precision R N m p F)

private theorem regroup {A B:Type*}[AddCommGroup A][AddCommGroup B]
    (h:A →+ B)(a x k:B)(j t q:A):
    a-(h t+x)+k = a-x+(k-h q)+h (j-t+q)-h j:=by
  rw [map_add,map_sub]
  abel

include shell head tag in
private theorem phase_data (b : Ink (Woods G (coarse R m p))) (hb : constantCoeff b = 0) :
    (precision R N m p F).transpose = (precision R N m p F) ∧ constantCoeff (relativeHaar R N m p hm F) = 0 ∧ constantCoeff (haar R N m p F) = 0 ∧
    constantCoeff (shot (step R m p) F (prediction R N m p) (ratio R) prior) = 0 ∧
    shot (step R m p) F (prediction R N m p) (ratio R) prior = (haar R N m p F) - (unscaled (step R m p) F (prediction R N m p) prior - (coarseAction R N m p F)) + bodyQ (Woods G (coarse R m p)) (precision R N m p F) ∧
    constantCoeff (relativePhase R N m p hm F prior b) = 0 := by
  have symm : (precision R N m p F).transpose = (precision R N m p F) := by
    unfold precision treeMatrix
    rw [transpose_submatrix,full_symmetric _ (age_sym (levels R) N (m+1) (fine R m p))]
  have posJ : constantCoeff (haar R N m p F) = 0 := floor_pres (T:=loom (slice R N m p F)) (by simp [loom])
    (by rw [jet_lead,unhaar_zero R.alloy.B.ratio,map_zero])
  have posA : constantCoeff (relativeHaar R N m p hm F) = 0 := by
    rw [jet_lead,stamp_o (step R m p) F (center R N m p hm F) (ratio R) R.alloy.B.ratio (map_zero _),map_zero]
  have zeroShot : constantCoeff (shot (step R m p) F (prediction R N m p) (ratio R) prior) = 0 :=
    floor_pres (T:=loom (overM G (step R m p) F)) (by simp [loom]) (flash_blank (pack_zero (step R m p) R.alloy.B.ratio))
  let T := unscaled (step R m p) F (prediction R N m p) prior - (coarseAction R N m p F)
  let P := shot (step R m p) F (prediction R N m p) (ratio R) prior
  have shotLaw : P = (haar R N m p F) - T + bodyQ (Woods G (coarse R m p)) (precision R N m p F) := by
    rw [show P = _ from shot_bill (step R m p) F (upper R N m) (lower R N m) (prediction R N m p) shell head ((levels R).blocks m p).branches
      (auxiliary R N m p hm) (age_sym (levels R) N (m+1) (fine R m p))]
    dsimp [T]; abel
  let φ := retool (shift R N m p hm F)
  have phiX : φ X = X := by simp [φ,retool,reroll]
  have F0 := local_zero_roll (1 : Matrix (Active G F) (Active G F) ℝ) path
    (leading R N m p hm F tag) (show (precision R N m p F) = (1 : Matrix (Active G F) (Active G F) ℝ).transpose*(precision R N m p F)*1 by simp)
  have eq : relativePhase R N m p hm F prior b = (relativeHaar R N m p hm F) - holdUp (Active G F) b +
      (bodyQ (Woods G (coarse R m p)) (precision R N m p F) - φ (bodyQ (Woods G (coarse R m p)) (precision R N m p F))) + φ P - φ (haar R N m p F) := by
    rw [shotLaw]
    exact regroup φ.toAddMonoidHom _ _ _ _ _ _
  have matchQ : constantCoeff (bodyQ (Woods G (coarse R m p)) (precision R N m p F)) = constantCoeff (φ (bodyQ (Woods G (coarse R m p)) (precision R N m p F))) :=
    sub_eq_zero.mp (by simpa only [φ,retool,map_sub] using F0)
  have hP : constantCoeff (φ P) = 0 := floor_pres (T:=φ) phiX zeroShot
  have cc : constantCoeff (relativePhase R N m p hm F prior b)=0 := by
    rw [eq]
    simp only [map_add,map_sub,posA,floor_pres (T:=holdUp (Active G F)) (by simp [holdUp]) hb,
      matchQ,sub_self,hP,floor_pres phiX posJ,add_zero]
  exact ⟨symm,posA,posJ,zeroShot,shotLaw,cc⟩

include shell head tag in
/-- The compensated centered exponent has no grade-zero vertex, including
for a generated vacuum component with independently specified coarse field. -/
theorem phase_zero (b : Ink (Woods G (coarse R m p))) (hb : constantCoeff b = 0) :
    constantCoeff (relativePhase R N m p hm F prior b) = 0 :=
  (phase_data R N m p hm F tag prior shell head b hb).2.2.2.2.2

include shell head in
theorem insertion (b : Ink (Woods G (coarse R m p))) (hb : constantCoeff b = 0)
    (w : Ink (Active G F ⊕ Woods G (coarse R m p))) :
    Wick (Woods G (coarse R m p)) ((model R N m p hm).covariance F tag) (raiseE (shot (step R m p) F (prediction R N m p) (ratio R) prior) * w) =
      raiseE b * Wick (Woods G (coarse R m p)) ((model R N m p hm).covariance F tag)
        (raiseE (relativePhase R N m p hm F prior b) * retool (shift R N m p hm F) w) := by
  let T := unscaled (step R m p) F (prediction R N m p) prior - (coarseAction R N m p F)
  let P := shot (step R m p) F (prediction R N m p) (ratio R) prior
  let φ := retool (shift R N m p hm F)
  obtain ⟨symm,posA,posJ,zeroShot,shotLaw,cc⟩ := phase_data R N m p hm F tag prior shell head b hb
  rw [genuine_cov R N m p hm F tag]
  exact OriginalTwoChartMarkedWick.moment (precision R N m p F) symm (invertible R N m p hm F tag)
    (spool (shift R N m p hm F)) (leading R N m p hm F tag) (relativeHaar R N m p hm F) (haar R N m p F) (φ T + holdUp (Active G F) b) T
    (relativePhase R N m p hm F prior b) P b posA posJ cc zeroShot hb rfl shotLaw rfl
    (area R N m p hm F tag) _ _ rfl

abbrev relativeMass (b : Ink (Woods G (coarse R m p))) :=
  Wick (Woods G (coarse R m p)) ((model R N m p hm).covariance F tag) (raiseE (relativePhase R N m p hm F prior b))

include shell head in
theorem empty (b : Ink (Woods G (coarse R m p))) (hb : constantCoeff b=0) :
    inside (step R m p) F (upper R N m) (prediction R N m p) (ratio R) prior = raiseE b * relativeMass R N m p hm F tag prior b := by
  unfold inside
  rw [← OriginalMarkedHeatCovariance.activeCovariance R N m p hm F tag]
  simpa only [map_one,mul_one] using insertion R N m p hm F tag prior shell head b hb 1



theorem original (simple:G.Simple)(b:Ink (Woods G (coarse R m p)))(hb:constantCoeff b=0):
    let P:=Winding.emera (actionW (levels R) (ratio R) N (m+1)) (fine R m p)
    inside (step R m p) F (upper R N m) (prediction R N m p) (ratio R) P =
      raiseE b * relativeMass R N m p hm F tag P b:=by
  intro P
  have price:=WilsonVacuumPreResetTorusUpperQuadratic.original R simple N (m+1) hm (fine R m p)
  exact empty R N m p hm F tag P price.1 price.2 b hb

end YM.Integration.WilsonVacuumPreResetStationaryChange
