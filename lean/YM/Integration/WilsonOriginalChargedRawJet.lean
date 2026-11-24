import YM.Integration.WilsonOriginalChargedRawRoster

/-! Each original curvature token carries its own Laurent shift into the physical forest derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedRawJet
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
local notation "fineSide" => R.family.side L period
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "C" => Stock.census V

open SignedOpeningMarkedVertices
open WilsonOriginalChargedRawRoster
local notation "unit" => (fun _ : V => (1:ℂ))
local notation "g₀" N:max => Pert.Asymptotics.regulatorRun R.family N period L
local notation "P₀" N:max => ActualOriginalQPackets.packets Q D u μ orders N

theorem room (N:ℕ)(a:Rows) : debt D (u:=u) a < commonPower (P₀ N) := by
  let e := (Fintype.equivFin (Rows)).symm
  let d (k:Fin (Fintype.card (Rows))) : ℕ := (-(ActualRunKernelPackets.fieldRank R (ActualOriginalQPackets.degree u) (e k):ℤ)).natAbs
  have h := Finset.le_sup (f:=d) (Finset.mem_univ (e.symm a))
  change debt D (u:=u) a < Finset.univ.sup d + 1
  simpa only [d,e.apply_symm_apply,Int.natAbs_neg,Int.natAbs_natCast,debt] using Nat.lt_succ_of_le h

private theorem cancellation (p h:ℕ)(hh:h<p)(t:ℝ) :
    (t:ℂ)^p*(t:ℂ)^(-(h:ℤ)) = (t:ℂ)^(p-h) := by
  by_cases ht:t=0
  · subst t
    simp [Nat.ne_of_gt (show 0<p by omega), Nat.ne_of_gt (show 0<p-h by omega)]
  have eq : ((p-h:ℕ):ℤ) = (p:ℤ) + -(h:ℤ) := by omega
  rw [←zpow_natCast (n:=p-h),eq,zpow_add₀ (Complex.ofReal_ne_zero.mpr ht),zpow_natCast]

def weight (N:ℕ)(s:(C).Mode)(a:Source D u) : ℂ :=
  SignedOpeningMarkedVertices.multiplier D u s a * (g₀ N:ℂ)^(debt D (u:=u) a.1)

theorem original (N:ℕ)(hN:L≤N)(vac:ℝ → Config G (fineSide) → ℝ)(x:TestSpace (O))
    (s:Hot (C))(t:ℝ)(U:Config G (fineSide)) :
    (NativePaidPacketColors.colors (P₀ N) vac x).mark s t U =
      ∑ a : Source D u, weight D u N s.val a *
        SignedRegisteredKernelPolynomial.primitive (atom Q D u μ orders unit x a)
          (origin D u a) (commonPower (P₀ N) - debt D (u:=u) a.1) t U := by
  change (t^commonPower (P₀ N)) • _ = _
  rw [WilsonOriginalChargedRawRoster.original Q D u μ orders N hN]
  simp only [Complex.real_smul,Complex.ofReal_pow,mul_sum]
  apply sum_congr rfl
  intro a _
  have ep := cancellation (commonPower (P₀ N)) (debt D (u:=u) a.1)
    (room Q D u μ orders N a.1) t
  simp only [WilsonOriginalChargedRawRoster.current,weight,SignedRegisteredKernelPolynomial.primitive,Complex.real_smul,Complex.ofReal_pow]
  rw [←ep]
  ring
variable {c : Side} {S : StepData c (R.family.side L period)} {clip : Clip} {path : PathData G} {z : ChartRatio G}
variable (K : Bulk.Kernel S clip path z) (F : Forest S.ratio) (M : Matrix (Woods G (R.family.side L period)) (Woods G c) ℝ)


/-- Every registered source row keeps its own Laurent degree when it enters the measured Gaussian. -/
theorem kernel (N:ℕ)(hN:L≤N)(vac : ℝ → Config G (fineSide) → ℝ)(x:TestSpace (O))
    (s:Hot (C))(B₀:fieldDir G c 1)(y:Precision.Key F G→ℝ)(j:ℕ)
    (hM:M=reveal G S F*((reveal G S F).transpose*M)) :
    Cloud.paint y (Assembly.kernelJet (Bulk.stage K F B₀) (Bulk.hinge F)
       (Bulk.markFn S F (NativePaidPacketColors.colors (P₀ N) vac x) s)
       (commonPower (P₀ N)+j)) =
      ∑ a : Source D u, weight D u N s.val a * (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B₀ y)
        (coeff (j+debt D (u:=u) a.1) (supplied Q D u μ orders unit K F M x a)):ℝ) := by
  let p := commonPower (P₀ N)
  let k (a:Source D u) := p-debt D (u:=u) a.1
  let funs (a : Source D u) := Bulk.posed S F (SignedRegisteredKernelPolynomial.primitive
    (atom Q D u μ orders unit x a) (origin D u a) (k a))
  have smooth (a:Source D u) : ContDiffAt ℝ ω (funs a) 0 :=
    SignedRegisteredKernelPolynomial.green F _ _ _
  have ray : Bulk.markFn S F (NativePaidPacketColors.colors (P₀ N) vac x) s =
      fun v => ∑ a : Source D u, weight D u N s.val a * funs a v :=
    funext fun v => original Q D u μ orders N hN vac x s v.1 (Work.F03.live F v.2)
  rw [ray,Assembly.reading,sumJet _ _ smooth]
  apply sum_congr rfl
  intro a _
  apply congrArg ((weight D u N s.val a)*·)
  rw [←Assembly.reading,SignedRegisteredKernelPolynomial.kernel K F]
  have hp : debt D (u:=u) a.1 < p := room Q D u μ orders N a.1
  have hk : k a ≤ p+j := by dsimp [k];omega
  have hidx : p+j-k a = j+debt D (u:=u) a.1 := by dsimp [k];omega
  change ((MvPolynomial.eval _ (coeff (p+j) ((X:Ink (Active G F⊕Woods G c))^(k a) * _)):ℝ):ℂ) = _
  rw [coeff_X_pow_mul',if_pos hk,hidx]
  let i := a.1.1.1
  let seed := chosen Q D u μ orders unit (fun _ => a.2.2.1) i (⟨a.1,rfl⟩,a.2.1)
  have eq := SignedOpeningSourceCurrent.series K F M i seed
    (SignedOriginalQCurvatureRows.tests D x (fun _ => a.2.2.2)) (lift (origin D u a))
    (show seed.head=seed.rank from rfl) hM
  simpa only [supplied,seed,i,wrap_lift,atom,SignedOriginalQCurvatureRows.currentAt] using
    congrArg (fun T : Ink (Active G F⊕Woods G c) =>
      ((MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B₀ y) (coeff (j+debt D (u:=u) a.1) T):ℝ):ℂ)) eq.symm

end YM.Integration.WilsonOriginalChargedRawJet
