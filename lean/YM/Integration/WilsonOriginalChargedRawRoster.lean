import YM.Integration.SignedOpeningMarkedVertices

/-! Restore every original Q token's own Laurent degree before the finite Gaussian and reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedRawRoster
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

open ActualRunKernelPackets
open SignedOpeningMarkedVertices
local notation "rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "unit" => (fun _ : V => (1:ℂ))
local notation "g₀" N:max => Pert.Asymptotics.regulatorRun R.family N period L

def debt (_ : ActualRunQlocalNativeTuple.Datum R period L n hn V) (a : rows) : ℕ := fieldRank R (ActualOriginalQPackets.degree u) a

def current (N:ℕ)(g:ℝ)(a:rows) : ℂ :=
  (g:ℂ)^(-(debt D (u:=u) a:ℤ)) * (g₀ N:ℂ)^(debt D (u:=u) a)

omit [Fintype V] in
/-- Reinstating a token's own physical source coordinate recovers its entire cleared group word. -/
theorem token (N:ℕ)(hN:L ≤ N)(a:rows)(x:TestSpace (O))(U:Config G (f)) :
    (ActualOriginalQPackets.token Q D u μ orders N a).read x U =
      (g₀ N:ℂ)^(debt D (u:=u) a) * SignedOriginalQCurvatureRows.field Q D u μ orders unit a x U := by
  have z : (g₀ N:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ActualRunKernelPackets.regulator_pos R N period L hN).ne'
  have row := SignedOriginalQCurvatureRows.measured Q D u μ orders unit N hN a.1.1 ⟨a,rfl⟩ x U
  change 1 * (g₀ N:ℂ)^(-(debt D (u:=u) a:ℤ)) *
    (ActualOriginalQPackets.token Q D u μ orders N a).read x U =
      SignedOriginalQCurvatureRows.field Q D u μ orders unit a x U at row
  rw [←row,one_mul,_root_.zpow_neg,zpow_natCast,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ z),one_mul]

/-- The full original group input now has its Laurent weights, for all test amplitudes and all configurations. -/
theorem original (N:ℕ)(hN:L ≤ N)(g:ℝ)(s:(Stock.census V).Mode)(x:TestSpace (O))(U:Config G (f)) :
    ((ActualOriginalQPackets.packets Q D u μ orders N).read x g U).part s =
      ∑ a : SignedOpeningMarkedVertices.Source D u, SignedOpeningMarkedVertices.multiplier D u s a *
        current D (u:=u) N g a.1 * ((SignedOpeningMarkedVertices.atom Q D u μ orders unit x a).unmasked U
          (SignedOpeningMarkedVertices.origin D u a):ℂ) := by
  have raw : ((ActualOriginalQPackets.packets Q D u μ orders N).read x g U).part s =
      ∑ a : rows, if s=(Stock.census V).fire a.1.1 then
        (g:ℂ)^(-(debt D (u:=u) a:ℤ)) * (ActualOriginalQPackets.token Q D u μ orders N a).read x U else 0 := by
    unfold ActualOriginalQPackets.packets
    rw [MarkedPackets.ofFin_read,Poly.part_sum]
    simp only [Poly.part_send]
    apply Fintype.sum_equiv (Fintype.equivFin (rows)).symm
    intro a
    rfl
  rw [raw]
  conv_rhs => rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro a _
  by_cases h:s=(Stock.census V).fire a.1.1
  · rw [if_pos h,token Q D u μ orders N hN,Fintype.sum_prod_type]
    simp only [←mul_assoc,current,SignedOriginalQCurvatureRows.field,
      SignedOpeningMarkedVertices.multiplier,h,if_true,SignedOpeningMarkedVertices.atom,SignedOpeningMarkedVertices.origin,mul_sum]
    apply sum_congr rfl
    intro w _
    apply sum_congr rfl
    intro b _
    ring
  · simp [h,SignedOpeningMarkedVertices.multiplier]

end YM.Integration.WilsonOriginalChargedRawRoster
