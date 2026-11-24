import YM.Integration.WilsonPositionSeparatedProfileMayerWickInputs

/-! The whole compensated Taylor observation is a finite polynomial on
the original independently filed Gaussian, on every genuine forest. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerWickWord
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
variable (X:Coat T F) (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (loc:I→Site f)
    (phase:I→Reading) (θ:ℝ) (y:(i:I) → run.family.label (d i))

def jetWord (j:ℕ):Normal.poly (Eye X):=kernelJet (0:Panels run d) (panel X run d loc)
    (material run d phase (fun i=>(run.family.labels.level (d i)).scaled θ⁻¹ (y i))) j

theorem component (z:Air f G) (j:ℕ):Cloud.paint (fun i=>z (tube X i)) (jetWord X run d loc phase θ y j)=
    (PowerSeries.coeff j (WilsonRetainedSignedStencilBooks.books run d F loc phase θ y z):ℝ):=by
  unfold jetWord
  rw [Comparison.RG02.Assembly.reading,Comparison.RG02.Assembly.translate,zero_add,WilsonPositionSeparatedProfileMayerWickInputs.original]
  rw [←WilsonRetainedSignedStencilBooks.graded run d F loc phase θ y z j]
  have hit:=Dict06.Series.radial_eq j ((smooth run d phase (fun i=>(run.family.labels.level (d i)).scaled θ⁻¹ (y i))).contDiffAt.of_le le_top) (restrict run d F loc z)
  exact hit.symm

theorem order (j:ℕ):(jetWord X run d loc phase θ y j).totalDegree≤j:=by
  unfold jetWord kernelJet wordL
  apply MvPolynomial.totalDegree_finsetSum_le;intro z _
  apply (MvPolynomial.totalDegree_mul _ _).trans;rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc _≤∑ _ : Fin j,1:=by
          apply Finset.sum_le_sum;intro a _
          change ((z a).elim (1:Normal.poly (Eye X)) MvPolynomial.X).totalDegree≤1
          cases z a <;> simp
       _=j:=by simp

def book (g:ℝ) (p:ℕ):Normal.poly (Eye X):=∑j∈range (p+1),MvPolynomial.C (g:ℂ)^j * jetWord X run d loc phase θ y j

theorem degree (g:ℝ) (p:ℕ):(book X run d loc phase θ y g p).totalDegree≤p:=by
  apply MvPolynomial.totalDegree_finsetSum_le;intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [←map_pow,MvPolynomial.totalDegree_C,zero_add]
  exact (order X run d loc phase θ y j).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem printed (g:ℝ) (p:ℕ) (z:Air f G): Cloud.paint (fun i=>z (tube X i)) (book X run d loc phase θ y g p)=
    (WilsonCoherentMayerSignedCharge.polynomial run d (F:=F) loc phase θ g y p z:ℝ):=by
  unfold book WilsonCoherentMayerSignedCharge.polynomial
  rw [map_sum,Complex.ofReal_sum];apply Finset.sum_congr rfl;intro j _
  rw [map_mul,component];simp [Cloud.paint]

theorem measured (H:Cash W s μ L Q o C T R) (temp:0≤Pressure.temp s) (χ:Chi) (i:Greenbelt.Reserve S) (tag:S.Choices) (g:ℝ) (p:ℕ):
    let X:=chamber T s o.K χ 1 ∅ i tag
    let word:=book X run d loc phase θ y g p
    ‖(∫ z:Air f G,(WilsonCoherentMayerSignedCharge.polynomial run d (F:=Greenbelt.allot i) loc phase θ g y p z:ℂ) ∂X.dice)-
      Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T (Greenbelt.allot i) tag s)
        (WilsonOriginalSignedSamplerMoment.symmetry T (Greenbelt.allot i) tag s) 0 word‖≤
      Rise.coin word*WilsonOriginalSignedSamplerMoment.fee T L P o p s:=by
  intro X word
  have h:=WilsonOriginalSignedSamplerMoment.original T H temp χ ∅ i tag word p (degree X run d loc phase θ y g p)
  have same:(∫z:Air f G,(WilsonCoherentMayerSignedCharge.polynomial run d (F:=Greenbelt.allot i) loc phase θ g y p z:ℂ) ∂X.dice)=
      ∫z:Air f G,Cloud.paint (fun u=>z (tube X u)) word ∂X.dice:=by
    apply integral_congr_ae;filter_upwards with z
    exact (printed X run d loc phase θ y g p z).symm
  rw [same];exact h

end YM.Integration.WilsonPositionSeparatedProfileMayerWickWord
