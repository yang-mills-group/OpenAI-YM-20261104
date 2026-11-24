import YM.Integration.SignedOriginalQCurvatureRows
import YM.Integration.SignedShiftedMeasuredCurrent
import YM.Integration.SignedRegisteredKernelPolynomial

/-! Absolute single-source Taylor coefficients of a genuine independent compact marked current
at the original finite forest. The insertion retains its own physical address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedOpeningSourceCurrent
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 Comparison.RG02.Cumulants AnalyticNext.QuarticMatch.Estimate PhysicalNext.Repeat.Legato
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power
open WilsonCoeffUV.Power.Roam WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {r : ℕ}

private theorem covariant {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (A : RG.Atom G r) (z : E) (L : E →L[ℝ] Z) (e : ℕ) :
    tuftV L (volumeR (current A z) e) = volumeR (current A (L z)) e := by
  have move {U : Type} (v : Gen E U) (w : Gen Z U)
      (h : ∀ l (x : Fin l → U), L (v l x) = w l x) :
      ply L.toLinearMap (moved r e v) = moved r e w := by
    funext i j x
    rw [ply_v]
    by_cases he : e ≤ i
    · by_cases hj : r+(i-e)=j
      · subst j;simpa [moved,he,Blue.shine,Function.comp_def] using h _ x
      · simp only [moved,if_pos he,Blue.shine,dif_neg hj,map_zero]
    · simp [moved,he]
  apply Prod.ext
  · funext n
    exact move _ _ fun l x => by simp [sapR,current,rayOne,map_sum,map_smul]
  · exact move _ _ fun l x => by simp [august,current,rayOne,map_sum,map_smul]

private theorem shade {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : RG.Atom G r)
    (hA : A.Invariant) (w : E) : shadeStar (current A w) := by
  intro L u x
  have ev (v : Fin r → G.Color) : (dip (current A w) L).poly v = L w*A.poly v := by
    rw [RG.Atom.poly,RG.Atom.poly,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    change L (A.coeff j • w)*_ = _
    rw [map_smul,smul_eq_mul]
    ring
  rw [ev,ev,hA]

variable {V : Type} [DecidableEq V] {D : V → ℕ} {c f : Side}
variable {S : StepData c f} {h : Clip} {path : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S h path O) (F : Forest S.ratio)
variable (M : Matrix (Woods G f) (Woods G c) ℝ)
local notation "ρ" => fderiv ℝ (K.b F) 0
variable (o : V) (a : Seed G (D o)) (X : Case D) (y₀ : Cover)
local notation "A₀" => colour a.path a.color a.weight a.quadrant
local notation "slot" => claim (D o) a.knob a.point
local notation "C₀" => current (A₀) (petal D o (slot))

def independent : Ink (Active G F ⊕ Woods G c) :=
  SignedMeasuredSourceSeries.probe S F M (ρ)
    (readO X (source D o (A₀) a.knob a.point a.head y₀) f)

/-- The charged row arising from the actual initial fixed-Q data has its native
head equal to its curvature rank. No division by a numerical field or test is used. -/
theorem series (ha : a.head = a.rank) (hM : M = reveal G S F * ((reveal G S F).transpose*M)) :
    independent K F M o a X y₀ =
      jet (fun u : Sloc S F G =>
        (dip (C₀) (touch X {o})).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F (ρ) u)) (wrap f y₀)) := by
  have cv : source D o (A₀) a.knob a.point a.head y₀ = shifted (volumeR (C₀) a.rank) y₀ := by
    unfold source cn
    rw [covariant,ha]
  have hs := SignedShiftedMeasuredCurrent.cleared S F M (ρ) (k:=0) (C₀) X y₀ a.rank 0 0
    (by omega) (by omega) (shade _ (fun u v=>OriginalMarkedSourceComet.invariant a.path a.color a.weight a.quadrant u v) _)
    hM (ρ).contDiff.contDiffAt (map_zero _)
  simpa only [independent,cv,pow_zero,one_mul] using hs

private theorem zero_response {r : ℕ} (T : RG.Atom G r) (b : Site f) (B : fieldDir G c 1)
    (y : Precision.Key F G→ℝ) (j : ℕ) :
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F)
      (Bulk.posed S F (fun _ U=> (T.unmasked U b : ℂ))) j) =
        (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B y) (coeff j
          (jet (fun u : Sloc S F G=>T.unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F (ρ) u)) b))) : ℝ) := by
  have fun_eq : (fun (_ : ℝ) (U : Config G f)=> (T.unmasked U b : ℂ))=SignedRegisteredKernelPolynomial.primitive T b 0 := by
    funext u U;simp only [SignedRegisteredKernelPolynomial.primitive,pow_zero,one_smul]
  rw [fun_eq]
  simpa only [pow_zero,one_mul] using SignedRegisteredKernelPolynomial.kernel K F T b B y 0 j

theorem coefficient (ha : a.head = a.rank) (hM : M = reveal G S F * ((reveal G S F).transpose*M))
    (B : fieldDir G c 1) (y : Precision.Key F G → ℝ) (j : ℕ) :
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F)
      (Bulk.posed S F (fun _ U => ((dip (C₀) (touch X {o})).unmasked U (wrap f y₀):ℂ))) j) =
        (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B y)
          (coeff j (independent K F M o a X y₀)) : ℝ) := by
  exact (zero_response K F (dip (C₀) (touch X {o})) (wrap f y₀) B y j).trans
    (congrArg (fun P : Ink (Active G F ⊕ Woods G c)=>((MvPolynomial.eval
      (SignedRegisteredKernelPolynomial.focus F B y) (coeff j P):ℝ):ℂ)) (series K F M o a X y₀ ha hM).symm)

end YM.Integration.SignedOpeningSourceCurrent
end
