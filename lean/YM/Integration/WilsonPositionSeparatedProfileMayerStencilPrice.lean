import YM.Integration.WilsonPositionSeparatedProfileMayerStencilColumns

/-! The independent Wick cost is prepaid on the fixed registered basis,
with no count of torus coordinates or separated sites. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerStencilPrice
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series
open WilsonPositionSeparatedProfileMayerStencilSites WilsonRetainedSignedStencilBasis
open WilsonPositionSeparatedProfileMayerStencilColumns
variable {I:Type} [Fintype I] (run:Run G) (d:I→ℕ)
def fee (j:ℕ):ℝ:=∑v:Mark run d,Rise.coin (cell run d v j)
def budget (p:ℕ):ℝ:=∑j∈range (p+1),(Fintype.card (I→Bool):ℝ)*fee run d j

private theorem cost (v:Mark run d) (j:ℕ):Rise.coin (cell run d v j)≤fee run d j:=by
  let f:Mark run d→ℝ:=fun i=>Rise.coin (cell run d i j)
  change f v≤∑i,f i
  exact Finset.single_le_sum (f:=f) (fun i _=>Rise.sign 0 (cell run d i j) (zero_le_one:0≤(1:ℝ))) (Finset.mem_univ v)

variable (φ:I→Reading) (θ:ℝ) (y:∀i,run.family.label (d i))
theorem charged (cap:∀i z,|φ i z|≤‖z‖) (j:ℕ):Rise.coin (registered run d φ θ y j)≤
    WilsonCoherentReportingPivot.mass run d θ y*((Fintype.card (I→Bool):ℝ)*fee run d j):=by
  unfold WilsonPositionSeparatedProfileMayerStencilColumns.registered
  apply (Rise.collect 0 (r:=1) zero_le_one _ _).trans
  calc _ ≤ ∑v:Mark run d,‖WilsonCoherentReportingFrame.charge run d θ y v.1‖*fee run d j:=by
          apply Finset.sum_le_sum;intro v _
          apply (Rise.funds 0 (r:=1) zero_le_one _ _).trans;rw [Rise.pay_C]
          apply mul_le_mul (WilsonRetainedSignedStencilBasis.charge run d φ cap θ y v.1 v.2)
          · exact cost run d v j
          · exact Rise.sign 0 (cell run d v j) zero_le_one
          · exact norm_nonneg _
       _ = _:=by
          rw [Fintype.sum_prod_type];simp only [sum_const,card_univ,nsmul_eq_mul]
          unfold WilsonCoherentReportingPivot.mass;rw [sum_mul];apply sum_congr rfl;intro v _;ring

def sheet (g:ℝ) (p:ℕ):Normal.poly (Letter run d):=∑j∈range (p+1),MvPolynomial.C ((g:ℂ)^j)*registered run d φ θ y j

theorem pooled (cap:∀i z,|φ i z|≤‖z‖) (g:ℝ) (hg:|g|≤1) (p:ℕ):Rise.coin (sheet run d φ θ y g p)≤
    WilsonCoherentReportingPivot.mass run d θ y*budget run d p:=by
  unfold sheet budget;rw [mul_sum];apply (Rise.collect 0 zero_le_one _ _).trans
  apply sum_le_sum;intro j _
  apply (Rise.funds 0 (r:=1) zero_le_one _ _).trans;rw [Rise.pay_C]
  have m:‖(g:ℂ)^j‖≤1:=by rw [norm_pow,Complex.norm_real,Real.norm_eq_abs];exact pow_le_one₀ (abs_nonneg _) hg
  exact (mul_le_mul_of_nonneg_right m (Rise.sign 0 _ zero_le_one)).trans (by rw [one_mul];exact charged run d φ θ y cap j)

def deposited (g:ℝ) (p:ℕ) (X:Coat T F) (loc:I→Site f):Normal.poly (Eye X):=Normal.exchange (wires (filed run d X loc)) (sheet run d φ θ y g p)

theorem preperiod (cap:∀i z,|φ i z|≤‖z‖) (g:ℝ) (hg:|g|≤1) (p:ℕ) (X:Coat T F) (loc:I→Site f):
    Rise.coin (deposited run d φ θ y g p X loc)≤WilsonCoherentReportingPivot.mass run d θ y*budget run d p:=
  (WilsonPositionSeparatedProfileMayerStencilSites.pay ..).trans (pooled run d φ θ y cap g hg p)

theorem degree (g:ℝ) (p:ℕ) (X:Coat T F) (loc:I→Site f):(deposited run d φ θ y g p X loc).totalDegree≤p:=by
  apply (Rise.ascent _ _).trans;apply MvPolynomial.totalDegree_finsetSum_le;intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans;rw [MvPolynomial.totalDegree_C,zero_add]
  exact (WilsonPositionSeparatedProfileMayerStencilColumns.order run d φ θ y j).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem printed (g:ℝ) (p:ℕ) (X:Coat T F) (loc:I→Site f) (z:Air f G):Cloud.paint (fun i=>z (tube X i)) (deposited run d φ θ y g p X loc)=
    (WilsonCoherentMayerSignedCharge.polynomial run d (F:=F) loc φ θ g y p z:ℝ):=by
  unfold deposited sheet WilsonCoherentMayerSignedCharge.polynomial
  rw [map_sum,map_sum,Complex.ofReal_sum];apply Finset.sum_congr rfl;intro j _
  rw [map_mul,Normal.exchange_c,map_mul,observed];simp [Cloud.paint]

end YM.Integration.WilsonPositionSeparatedProfileMayerStencilPrice
