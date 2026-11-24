import YM.Integration.WilsonPositionSeparatedProfileMayerWickWord
import YM.Integration.WilsonCoherentMayerOldMarginal

/-! The original covariance correction at a labelled positive Mayer decoration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelPolynomial
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

variable (X:Coat T F)

def coordinate (e:Bond f) (free:e∉F.trunks) (a:G.ColorIndex) : Normal.poly (Eye X) :=
  MvPolynomial.X (Native.lineEquiv (G:=G) F X.x (⟨e,free⟩,a))

theorem read_coordinate (e:Bond f) (free:e∉F.trunks) (a:G.ColorIndex) (z:Air f G) :
    Cloud.paint (fun i=>z (tube X i)) (coordinate X e free a)=(z (e,a):ℂ) := by
  simp only [coordinate,Cloud.paint,MvPolynomial.aeval_X]
  rfl

def quadratic (q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks) :
    Normal.poly (Eye X) :=
  MvPolynomial.C ((1/2:ℝ):ℂ) *
    ∑ a:G.ColorIndex, coordinate X q.2.1 first a *
      ∑ b:G.ColorIndex, MvPolynomial.C ((combo q.2.1 q.2.2 (X.finale q.1) a b:ℝ):ℂ) *
        coordinate X (arrive q.2.1 q.2.2) last b

theorem read_quadratic (q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks) (z:Air f G) :
    Cloud.paint (fun i=>z (tube X i)) (quadratic X q first last)=(X.qunique z q:ℂ) := by
  simp only [quadratic,map_mul,map_sum,read_coordinate,Cloud.paint,MvPolynomial.aeval_C,
    Coat.qunique,Coat.circle,Complex.ofReal_mul,Complex.ofReal_sum]
  rfl

theorem degree (q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks) :
    (quadratic X q first last).totalDegree≤2 := by
  unfold quadratic
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have inner:(∑ b:G.ColorIndex,MvPolynomial.C ((combo q.2.1 q.2.2 (X.finale q.1) a b:ℝ):ℂ) *
      coordinate X (arrive q.2.1 q.2.2) last b).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le;intro b _
    apply (MvPolynomial.totalDegree_mul _ _).trans;simp [coordinate]
  have outer:(coordinate X q.2.1 first a).totalDegree≤1:=by simp [coordinate]
  omega

/-- The exact unmarked covariance head at the physical marked experiment. -/
def label (q:Ledger f 2) : Head S := .inr (.inr (.inl (.inr (.inr (.inr (.inr (.inr (.inr q))))))))

theorem charged (H:Cash W s μ L Q o C T R) (q:Ledger f 2)
    (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks) (z:Air f G) :
    (Mayer.exponent H X z (label (S:=S) q):ℂ)=
      (X.aperture R.beta z o.a q.2.1:ℂ) *
      (X.aperture R.beta z o.a (arrive q.2.1 q.2.2):ℂ) *
      Cloud.paint (fun i=>z (tube X i)) (quadratic X q first last) := by
  rw [read_quadratic];change ((X.chain R.beta z o.a q:ℝ):ℂ)=_
  simp [Coat.chain]

end YM.Integration.WilsonCoherentMayerFuelPolynomial
