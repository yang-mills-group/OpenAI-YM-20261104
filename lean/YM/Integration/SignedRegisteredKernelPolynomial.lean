import YM.Integration.SignedMarkedChartGerm
import YM.Integration.SignedFormalPowerLayers

/-! The actual RG02 finite Marked kernel polynomial, evaluated at each independent coarse and Gaussian configuration, agrees with the correct coefficient of the same rooted native heat current. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedRegisteredKernelPolynomial
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AnalyticNext.QuarticMatch.Estimate PhysicalNext.Repeat.Legato
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} {S : StepData c f} {h : Clip} {path : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S h path O) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ)
local notation "D₀" => fderiv ℝ (K.b F) 0

def focus (B : fieldDir G c 1) (y : Precision.Key F G→ℝ) : Sloc S F G :=
  Sum.elim ((vcloth S F G).symm (tape y)) ((arm G c 1).symm B)

private theorem scaled (t : ℝ) (z : Sloc S F G) : SignedMarkedChartGerm.chart S F (D₀) (t • z)=t • SignedMarkedChartGerm.chart S F (D₀) z := by
  have hL : leftArm (t • z)=t • leftArm z := rfl
  have hR : rightArm (t • z)=t • rightArm z := rfl
  simp only [SignedMarkedChartGerm.chart,badge,sedan,hL,hR,map_smul,smul_add,Prod.smul_mk]

/-- The complete Gaussian and coarse directions are the authentic `Bulk.translated`, including the selected statistical rotation. -/
theorem registered (B : fieldDir G c 1) (y : Precision.Key F G→ℝ) :
    Bulk.translated K F B y=(1,SignedMarkedChartGerm.chart S F (D₀) (focus F B y)) := by
  rw [Bulk.footing]
  change ((1:ℝ),B,(D₀) B+tape y)=(1,arm G c 1 ((arm G c 1).symm B),
    vcloth S F G ((vcloth S F G).symm (tape y)) + (D₀) (arm G c 1 ((arm G c 1).symm B)))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [add_comm ((D₀) B)]

private def field {r : ℕ} (T : Atom G r) (a : Site f) (u : Work.F03.ChartVars F G) : ℝ := T.unmasked (Work.F03.live F u) a

private theorem field_green {r : ℕ} (T : Atom G r) (a : Site f) : ContDiffAt ℝ ω (field F T a) 0 := by
  have hφ := (Work.F03.inclusion_smooth F (G:=G)).snd
  have H := (Cargo.effective T a).contDiffAt.comp (0:Work.F03.ChartVars F G) hφ
  apply H.congr_of_eventuallyEq
  filter_upwards [Work.F03.inclusion_works F (G:=G)] with u hu
  exact congrArg (fun U=>T.unmasked U a) hu.symm

private theorem echo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E→ℝ}
    (h : ContDiffAt ℝ ω f 0) (k : ℕ) (v : E) :
    Assembly.jet (Complex.ofRealCLM ∘ f) k v=(Assembly.jet f k v:ℝ) := by
  unfold Assembly.jet
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (h.of_le le_top) le_rfl]
  exact (Complex.ofRealCLM.map_smul ((k.factorial:ℝ)⁻¹) (iteratedFDeriv ℝ k f 0 (fun _=>v))).symm

def primitive {r : ℕ} (T : Atom G r) (a : Site f) (t : ℕ) (u : ℝ) (V : Config G f) : ℂ := u^t • (T.unmasked V a:ℂ)

/-- The genuine cleared input is analytic on the measured original forest. -/
theorem green {r : ℕ} (T : Atom G r) (a : Site f) (t : ℕ) : ContDiffAt ℝ ω (Bulk.posed S F (primitive T a t)) 0 := by
  let f := field F T a
  have h : ContDiffAt ℝ ω (fun u:Bulk.Joint S F (G:=G)=>f u.2) 0 := (field_green F T a).comp (f:=@Prod.snd ℝ (Work.F03.ChartVars F G)) (0:Bulk.Joint S F (G:=G)) contDiffAt_snd
  exact (contDiffAt_fst.pow t).smul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 h)

/-- Exact finite radial identity prior to any independent formal-coordinate identification. -/
theorem kernel {r : ℕ} (T : Atom G r) (a : Site f) (B : fieldDir G c 1) (y : Precision.Key F G→ℝ) (t k : ℕ) :
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.posed S F (primitive T a t)) k)=
    (MvPolynomial.eval (focus F B y) (coeff k ((X:Ink (Active G F⊕Woods G c))^t*
      jet (fun u : Sloc S F G=>T.unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F (D₀) u)) a))):ℝ) := by
  let A := focus F B y
  let j := SignedMarkedChartGerm.chart S F (D₀)
  let f₀ := field F T a
  let f₁ : Bulk.Joint S F (G:=G)→ℝ := fun u=>f₀ u.2
  have h₀ := field_green F T a
  have h₁ : ContDiffAt ℝ ω f₁ 0 := h₀.comp (f:=@Prod.snd ℝ (Work.F03.ChartVars F G)) (0:Bulk.Joint S F (G:=G)) contDiffAt_snd
  have h₂ : ContDiffAt ℝ ω (Complex.ofRealCLM ∘ f₁) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 h₁
  have hj : Green j := (badge_green S F).prodMk (sedan_green S F (D₀) (D₀).contDiff.contDiffAt).fst
  have hj0 : j 0=0 := by
    simpa only [zero_smul] using scaled K F (0:ℝ) (0:Sloc S F G)
  have h₃ : Green (f₀ ∘ j) := (show ContDiffAt ℝ ω f₀ (j 0) from hj0.symm ▸ h₀).comp 0 hj
  rw [Assembly.reading]
  change Assembly.jet (fun u:Bulk.Joint S F (G:=G)=>u.1^t • (Complex.ofRealCLM ∘ f₁) u) k (Bulk.translated K F B y)=_
  rw [registered, SignedFormalPowerLayers.shifted h₂ t k _ rfl,coeff_X_pow_mul']
  by_cases ht:t≤k
  · rw [if_pos ht,if_pos ht,echo h₁]
    have hv : (fun s:ℝ=>f₁ (s • (1,j A)))=fun s:ℝ=>(f₀ ∘ j) (s • A) := by
      funext s
      change f₀ (s • j A)=f₀ (j (s • A))
      exact congrArg f₀ (scaled K F s A).symm
    let L : ℝ→L[ℝ] Bulk.Joint S F (G:=G) := ContinuousLinearMap.toSpanSingleton ℝ (1,j A)
    let H : ℝ→L[ℝ] Sloc S F G := ContinuousLinearMap.toSpanSingleton ℝ A
    have hh : f₁ ∘ L=(f₀ ∘ j) ∘ H := hv
    have ht₁ := Assembly.jet_continuous_right L (h₁.of_le (le_top (a:=((k-t:ℕ):WithTop ℕ∞)))) (1:ℝ)
    have ht₂ := Assembly.jet_continuous_right H (h₃.of_le (le_top (a:=((k-t:ℕ):WithTop ℕ∞)))) (1:ℝ)
    rw [hh] at ht₁
    simp only [L,H,ContinuousLinearMap.toSpanSingleton_apply,one_smul] at ht₁ ht₂
    rw [show Assembly.jet f₁ (k-t) (1,j A)=Assembly.jet (f₀ ∘ j) (k-t) A from ht₁.symm.trans ht₂]
    rw [rayon];rfl
  · simp [ht]

/-- For a supplied true joint Riesz current, compare one actual finite marked input generator *polynomial* at its original grade to the independent same-data registered finite formal kernel before any Gaussian integration. -/
theorem coefficient {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Comet G V r) (L : V→L[ℝ]ℝ) (B : fieldDir G c 1) (y : Precision.Key F G→ℝ) (e b t n : ℕ) (ht : b+e=r+t)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) :
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.posed S F (primitive (dip P L) 0 t)) (b+n))=
      (MvPolynomial.eval (focus F B y) (coeff n (retool (shore S F M (D₀)) (loom (camSlice G S F M)
       (flash (ply L.toLinearMap ((volumeR P e).1 f)))))):ℝ) := by
  rw [kernel]
  have hv := SignedMarkedChartGerm.cleared S F M (D₀) P L e b t ht hM (D₀).contDiff.contDiffAt (map_zero _)
  rw [←hv,coeff_X_pow_mul',if_pos (Nat.le_add_right b n),Nat.add_sub_cancel_left]

end YM.Integration.SignedRegisteredKernelPolynomial
