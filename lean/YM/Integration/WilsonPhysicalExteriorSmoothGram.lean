import YM.Integration.WilsonPhysicalExteriorFormalPrice
import YM.Integration.MSSeparatedSmearedTreeGram

/-! The determining compact smooth far test can be presold, before the
subtraction log and all perturbative orders. We invert the actual measured
Gram directly over ℂ[log], then evaluate at that log. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSmoothGram
open Set Filter Function Polynomial Matrix Pert Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone MS.Logarithm
open FVA2 FVA2.ColorCode Extra.FD
open WilsonPhysicalExteriorFormalGram (word charge gear)
open scoped Classical BigOperators Topology

variable {G:Gauge} (V:Warehouse G) {B:MS.Local.Physical.Deck G}{A:Booked B}
variable (M:MS_Data G A)(h:ℕ)(g:Test 2)
local notation "I" => Glyph B h
local notation "K₀" => Matrix I I ℂ
local notation "Kp" => Matrix I I (Polynomial ℂ)

theorem reading (k:ℕ)(a b:I) : Ready (fun u :ℝ=>MSSeparatedTestGram.matrix M h u k g a b) := by
  let F(v:ℝ)(z:Points 2) := MSDeckProbeGram.raw M ![a,b] z v k
  apply MSExteriorFiniteScales.test_ready g F
  · exact MSExteriorFiniteScales.tour_polynomial M (word h a b) (fun z : ↥(tsupport g)=>Fountain.metric z.val)
      (fun z=>Fountain.metric_conf (g.tsupport_subset z.property)) k
  · intro j z hz
    have chart : Continuous (Fountain.metric (m:=2)):=by
      apply continuous_pi
      intro i
      exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
        ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2=>E4)).continuous)
    exact (Dial.contin M (word h a b) (Fountain.metric z) (Fountain.metric_conf (g.tsupport_subset hz)) Finset.univ k j).1.comp chart.continuousAt

def row (k:ℕ)(a b:I) : Polynomial ℂ :=
  if k=0 then Polynomial.C (MSSeparatedTestGram.matrix M h 0 0 g a b)
  else (MSExteriorFiniteScales.complex_polynomial (reading M h g k a b)).choose

include V in
theorem evaluated_row (k:ℕ)(a b:I)(u:ℝ) :
    (row M h g k a b).eval (u:ℂ)=MSSeparatedTestGram.matrix M h u k g a b := by
  by_cases hk:k=0
  · subst k
    rw [row,if_pos rfl,eval_C]
    exact congrFun (congrFun (MSSeparatedTestGram.scale V M h 0 u g) a) b
  · rw [row,if_neg hk]
    exact ((MSExteriorFiniteScales.complex_polynomial (reading M h g k a b)).choose_spec u).symm

def bookP : PowerSeries Kp := PowerSeries.mk (row M h g)
def measured (v:ℝ) : PowerSeries K₀ := PowerSeries.mk (fun k=>MSSeparatedTestGram.matrix M h v k g)
def evalM (v:ℝ) : Kp →+* K₀ := (Polynomial.evalRingHom (v:ℂ)).mapMatrix
def seed (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) : Kpˣ :=
  Units.map (Polynomial.C (R:=ℂ)).mapMatrix.toMonoidHom hg.unit

include V in
theorem field (v:ℝ) : PowerSeries.map (evalM (B:=B) h v) (bookP M h g)=measured M h g v := by
  apply PowerSeries.ext;intro k;ext a b
  rw [PowerSeries.coeff_map,bookP,measured,PowerSeries.coeff_mk,PowerSeries.coeff_mk]
  exact evaluated_row V M h g k a b v

theorem floor (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) :
    PowerSeries.constantCoeff (bookP M h g)=(seed M h g hg:Kp) := by
  rw [bookP,PowerSeries.constantCoeff_mk]
  apply Matrix.ext;intro a b
  change row M h g 0 a b=Polynomial.C ((hg.unit:K₀) a b)
  rw [row,if_pos rfl,IsUnit.unit_spec]

def inverseP (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) : PowerSeries Kp :=
  (bookP M h g).invOfUnit (seed M h g hg)
def evaluatedInverse (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g))(v:ℝ) : PowerSeries K₀ :=
  PowerSeries.map (evalM (B:=B) h v) (inverseP M h g hg)

include V in
theorem inverse (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g))(v:ℝ) :
    measured M h g v*evaluatedInverse M h g hg v=1 ∧ evaluatedInverse M h g hg v*measured M h g v=1 := by
  rw [←field V M h g v,evaluatedInverse]
  constructor
  · rw [←map_mul,inverseP,PowerSeries.mul_invOfUnit _ _ (floor M h g hg),map_one]
  · rw [←map_mul,inverseP,PowerSeries.invOfUnit_mul _ _ (floor M h g hg),map_one]

/-- The actual held test is used at the dilated, physically separated
configuration, with the independently supplied outer field charge. -/
def far (μ s:ℝ) : PowerSeries K₀ := PowerSeries.mk fun k a b=>
  g.applyTo (fun z=>charge h s b*MSExteriorDilation.moment M (word h a b) μ
      (MSExteriorDilation.stretch s (Fountain.metric z)) k)

theorem scales (μ s:ℝ) :
    far M h g μ s=PowerSeries.C (gear (B:=B) h (-s))*measured M h g (μ+s) := by
  apply PowerSeries.ext;intro k
  rw [PowerSeries.coeff_C_mul,far,measured,PowerSeries.coeff_mk,PowerSeries.coeff_mk]
  ext a b
  rw [gear,Matrix.diagonal_mul,MSSeparatedTestGram.matrix,←OPETreeTests.scalar]
  apply OPETreeTests.on_support
  intro z hz
  have he:=MSExteriorDilation.scales M (word h a b) (μ+s) s (Fountain.metric z)
    (Fountain.metric_conf (g.tsupport_subset hz)) k
  have hw: MSExteriorDilation.weight (word h a b)=a.size+b.size := by
    rw [MSExteriorDilation.weight, Fin.sum_univ_two];rfl
  rw [add_sub_cancel_right,hw,Nat.cast_add] at he
  change charge h s b * MSExteriorDilation.moment M (word h a b) μ (MSExteriorDilation.stretch s (Fountain.metric z)) k = charge h (-s) a * MSExteriorDilation.moment M (word h a b) (μ+s) (Fountain.metric z) k
  rw [he,←mul_assoc]
  congr 1
  unfold charge MSExteriorDilation.power
  norm_cast
  rw [←Real.exp_add];congr 1;push_cast;ring

def decoder (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g))(μ s:ℝ) : PowerSeries K₀ :=
  evaluatedInverse M h g hg (μ+s)*PowerSeries.C (gear (B:=B) h s)

private theorem cancel (s:ℝ) : gear (B:=B) h s*gear h (-s)=1 := by
  rw [gear,gear,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
  congr 1;funext a
  change ((Real.exp ((a.size:ℝ)*s):ℝ):ℂ)*((Real.exp ((a.size:ℝ)*(-s)):ℝ):ℂ)=1
  norm_cast;rw [←Real.exp_add];simp

include V in
theorem corrected (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g))(μ s:ℝ) :
    far M h g μ s*decoder M h g hg μ s=1 ∧ decoder M h g hg μ s*far M h g μ s=1 := by
  obtain ⟨ha,hb⟩:=inverse V M h g hg (μ+s)
  have h₁:=cancel (B:=B) h s
  have h₂ : gear (B:=B) h (-s)*gear h s=1 := by simpa only [neg_neg] using cancel (B:=B) h (-s)
  rw [scales M h g μ s,decoder]
  constructor
  · rw [mul_assoc,←mul_assoc (measured M h g (μ+s)),ha,one_mul,←map_mul,h₂,map_one]
  · rw [mul_assoc,←mul_assoc (PowerSeries.C (gear h s)),←map_mul,h₁,map_one,one_mul,hb]

end YM.Integration.WilsonPhysicalExteriorSmoothGram
