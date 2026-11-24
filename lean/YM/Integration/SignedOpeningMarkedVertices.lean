import YM.Integration.SignedOpeningSourceCurrent
import YM.Integration.SignedFrozenFormalSource
import YM.Integration.NativeWilsonChargedPrescribed
import YM.Integration.SignedOriginalPostedCoefficient

/-! Native nonempty Taylor letters of the original Wilson opening on independently located,
individually charged MS fields, including the complete nonlinear finite group input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedOpeningMarkedVertices
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Comparison.Density.RenderM NativePaidPacketColors MergeProof MergeProof.Accent
open PertExtension Series Series.Radial Series.Tested RegulatorIR RegulatorIR.FVAAlt2
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open ActualRunCalibrationTests OriginalSourceJetAddresses FundedOriginalMarkedInput
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

private theorem sumJet {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (c : I → ℂ) (f : I → E → ℂ) (smooth : ∀ i, ContDiffAt ℝ ω (f i) 0) (j : ℕ) (v : E) :
    Assembly.jet (fun u => ∑ i, c i*f i u) j v = ∑ i, c i*Assembly.jet (f i) j v := by
  let L (i:I) := c i • ContinuousLinearMap.id ℝ ℂ
  have hs (i : I) : ContDiffAt ℝ ω (L i ∘ f i) 0 := (L i).contDiff.contDiffAt.comp _ (smooth i)
  calc
    _ = ∑ i, Assembly.jet (L i ∘ f i) j v := by
      change Assembly.jet (fun a => ∑ i,(L i ∘ f i) a) j v = _
      unfold Assembly.jet
      rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hs i).of_le le_top)]
      simp [smul_sum]
    _ = _ := sum_congr rfl fun i _ => (Assembly.jet_apply_left (L i) (f i) j
      ((smooth i).of_le le_top) v).symm

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {period L n : ℕ} {hn : n ≤ L}
variable {V : Type} [Fintype V] [DecidableEq V]
variable (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R period L n hn V)
variable (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (scale : V → ℂ)
local notation "O" => ActualRunQlocalNativeTuple.orbit D
local notation "f" => R.family.side L period
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "C" => Stock.census V

abbrev Source := (r : Rows) × (OriginalSourceJetAddresses.Word (RG05Readout.Native.depth (D.choice r.1.1).2.1) × (Bool × Bool))

def multiplier (s : (C).Mode) (a : Source D u) : ℂ :=
  if s = (C).fire a.1.1.1 then phase a.2.2.1 * phase a.2.2.2 else 0

def atom (x : TestSpace (O)) (a : Source D u) :=
  let i := a.1.1.1
  dip (SignedOriginalQCurvatureRows.currentAt Q D u μ orders scale i (⟨a.1,rfl⟩,a.2.1) (fun _ => a.2.2.1))
    (touch (SignedOriginalQCurvatureRows.tests D x (fun _ => a.2.2.2)) {i})

def origin (a : Source D u) : Site (f) := ActualRunQlocalNativeTuple.root D a.1.1.1

theorem configured (N : ℕ) (hN : L ≤ N) (x : TestSpace (O)) (s : (C).Mode) (U : Config G (f)) :
    ((ActualOriginalQFrozenInput.packets Q D u μ orders N).read (fun i => scale i • x i) 1 U).part s =
      ∑ a : Source D u, multiplier D u s a * ((atom Q D u μ orders scale x a).unmasked U (origin D u a):ℂ) := by
  rw [SignedOriginalQCurvatureRows.complete Q D u μ orders scale N hN]
  conv_rhs => rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro a _
  by_cases h : s=(C).fire a.1.1
  · rw [if_pos h,Fintype.sum_prod_type]
    simp only [SignedOriginalQCurvatureRows.field,multiplier,h,if_true,atom,origin]
  · simp [multiplier,h]

variable {c : Side} {S : StepData c (R.family.side L period)} {clip : Clip} {path : PathData G} {z : ChartRatio G}
variable (K : Bulk.Kernel S clip path z) (F : Forest S.ratio) (M : Matrix (Woods G (R.family.side L period)) (Woods G c) ℝ)

def supplied (x : TestSpace (O)) (a : Source D u) : Ink (Active G F ⊕ Woods G c) :=
  SignedOpeningSourceCurrent.independent K F M a.1.1.1
    (FundedOriginalMarkedInput.chosen Q D u μ orders scale (fun _ : V => a.2.2.1) a.1.1.1
      (⟨⟨a.1,rfl⟩,a.2.1⟩ : FundedOriginalMarkedInput.Count D u a.1.1.1))
    (SignedOriginalQCurvatureRows.tests D x (fun _ : V => a.2.2.2)) (lift (origin D u a))

theorem kernel (N : ℕ) (_hN : L ≤ N) (_point : BudgetPoint) (vac : ℝ → Config G (f) → ℝ)
    (_hM : M = reveal G S F * ((reveal G S F).transpose*M))
    (s : Hot (C)) (x : TestSpace (O)) (B₀ : fieldDir G c 1) (y : Precision.Key F G → ℝ) (j : ℕ) :
    let P := ActualOriginalQFrozenInput.packets Q D u μ orders N
    let W := colors P vac (fun i => scale i • x i)
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B₀) (Bulk.hinge F) (Bulk.markFn S F W s) (W.power s+j)) =
      ∑ a : Source D u, multiplier D u s.val a *
        (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B₀ y) (coeff j (supplied Q D u μ orders scale K F M x a)) : ℝ) := by
  intro P W
  have H := ActualOriginalQFrozenInput.packets_paid Q D u μ orders N 1 _point (fun _ => 1) 1
    zero_lt_one (fun _ => zero_lt_one)
  let f₁ (a : Source D u) (v : Bulk.Joint S F (G:=G)) : ℂ :=
    (atom Q D u μ orders scale x a).unmasked (Work.F03.live F v.2) (origin D u a)
  have posed (H : ℝ → Config G (R.family.side L period) → ℂ) :
      Bulk.posed S F H = fun v => H v.1 (Work.F03.live F v.2) := rfl
  have hf (a : Source D u) : ContDiffAt ℝ ω (f₁ a) 0 := by
    simpa only [posed,SignedRegisteredKernelPolynomial.primitive,f₁,pow_zero,one_smul] using
      SignedRegisteredKernelPolynomial.green F (atom Q D u μ orders scale x a) (origin D u a) 0
  have measured : (fun v : Bulk.Joint S F (G:=G) =>
        (P.read (fun i => scale i • x i) 1 (Work.F03.live F v.2)).part s.val) =
      fun v => ∑ a : Source D u, multiplier D u s.val a * f₁ a v :=
    funext fun v => configured Q D u μ orders scale N _hN x s.val (Work.F03.live F v.2)
  have input := SignedFrozenFormalSource.remove F H one_ne_zero (show P.powerCap=0 from rfl)
    K vac (fun i => scale i • x i) s B₀ j
  change Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B₀) (Bulk.hinge F) (Bulk.markFn S F W s) (1+j)) = _
  rw [input,measured,Assembly.reading,sumJet _ _ hf]
  apply sum_congr rfl
  intro a _
  apply congrArg ((multiplier D u s.val a)*·)
  rw [←Assembly.reading]
  let i := a.1.1.1
  let t := chosen Q D u μ orders scale (fun _ => a.2.2.1) i (⟨a.1,rfl⟩,a.2.1)
  have eq := SignedOpeningSourceCurrent.coefficient K F M i t
    (SignedOriginalQCurvatureRows.tests D x (fun _ => a.2.2.2)) (lift (origin D u a))
    (show t.head=t.rank from rfl) _hM B₀ y j
  simpa only [supplied,t,i,wrap_lift,f₁,posed,atom,SignedOriginalQCurvatureRows.currentAt] using eq


end YM.Integration.SignedOpeningMarkedVertices
end
