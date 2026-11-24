import YM.Integration.WilsonOriginalSignedSamplerChart
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Operators
import YM.Push.FREE_RESOLVENT.AffineResolvent
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics

/-! The remaining path truncation for a free covariance entry at identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedPathCut
open Function Filter Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix Bloch
open Pressure Pressure.Testing PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent
open FreeResolvent.Affine FreeResolvent.TestD Work.F03 AnalyticBridge.GaussianFieldAlignment
open scoped Topology Classical BigOperators

def price (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (A σ : ℝ) : ℝ :=
  let a := headGap G P K p
  let V := load G P K p 0 A σ
  let M := stageCost G P K p 0 A σ
  let μ := phasePrice G P K 0 A σ
  let C := meter 0 0 M 1 (rise V a) * drain 0
  C^2 * (2 * μ^2)

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)

theorem entry {P : Teller G} (fund : P.Funds S T) (geo : Bid.Larger (G:=G) S)
    (F : Forest S.ratio) (tag : S.Choices) (l : ℕ) (i j : Key F G) :
    |(primary S F tag T.high T.up (shorter l) 0)⁻¹ i j -
      (primary S F tag T.high T.up all 0)⁻¹ i j| ≤
    price G S.patch S.kernel T.high P.top.paths P.top.width * Real.exp (-(P.top.width/4)*l) := by
  obtain ⟨Λ,_,hW,_⟩ := fund.feeds
  have hW₀ : T.up.Bounds T.high P.top.width P.top.paths Λ := by rw [fund.high]; exact hW
  have h := shortening (W:=T.up) F tag P.top.width_pos P.top.paths_pos.le (path_sheet T hW₀) geo T.high 0 l (u:=0) (le_refl _)
  let γ := footprint G S.patch S.kernel T.high 0 P.top.paths P.top.width
  have hγ : 0 ≤ γ := (situate G S.patch S.kernel T.high (k:=0) P.top.width_pos P.top.paths_pos.le).pos.le
  have e := ((h.bound [] (by simp)).row.entry i j)
  simp only [Mark.pay,one_mul,zeroth,Pi.sub_apply,Matrix.sub_apply] at e
  have hw : 1 ≤ (native c).weight γ (theta _ F i) (theta _ F j) := by
    simpa only [Cost.weight_zero] using (native c).weight_mono hγ (theta _ F i) (theta _ F j)
  simp only [TestD.action,FreeResolvent.resolve,zero_smul,add_zero] at e
  apply (le_mul_of_one_le_left (abs_nonneg _) hw).trans
  exact e.trans_eq (by simp [price,tagPrice]; ring)

theorem payable (L : Side) (P : Teller G) (d : ℝ) :
    ConnectedActivityE6.Rate G L d (fun s => price G S.patch S.kernel T.high P.top.paths P.top.width *
      Real.exp (-(P.top.width/4)*Stores.till s)) :=
  (ConnectedActivityE6.Rate.cutoff (G:=G) (L:=L) (a:=d) (δ:=P.top.width/4) (div_pos P.top.width_pos (by norm_num))).mul_left _

end YM.Integration.WilsonOriginalSignedPathCut
