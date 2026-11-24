import YM.Integration.WilsonPositionSeparatedProfileMayerMasks
import YM.Integration.WilsonOriginalSignedSamplerMoment
import YM.LocalLTE.Weft.Valued

/-! On the surviving zero-decoration sector even forced marked heads leave
all Gaussian stores empty at flat boundary. Their marked integrands remain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerFlat
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

open WilsonCoherentMayerHearing WilsonCoherentMayerOccurrences
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws Next.Rank PhysicalNext.Repeat.Malachite
open Comparison.RG02.Cumulants

private theorem right (prior:Team R) : (prior.signs S).toLeft=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hit
  obtain ⟨m,_,eq⟩:=Finset.mem_image.mp (Finset.mem_toLeft.mp hit)
  cases hw:m.turn <;> simp [hw,Wing.badge] at eq

private theorem stored (prior:Team R) : roster (prior.signs S)=(⟨∅,∅,∅⟩:Stores S):=by
  rw [roster,right,Finset.biUnion_empty]
  rfl

theorem same (prior:Team R) (χ:Chi) (s K:ℝ) (temp:0≤Pressure.temp s) (i:Greenbelt.Reserve S) (tag:S.Choices) :
    ((planted (prism T s χ K (1:Config G c) (Greenbelt.allot i)) (prior.signs S)).taggedL tag)=
      chamber T s K χ 1 ∅ i tag :=by
  have hf:RG.flags (Pressure.temp s) (1:Config G c)=∅:=
    (show ∅=RG.flags (Pressure.temp s) (1:Config G c) from (prism T s χ K (1:Config G c) (Greenbelt.allot i)).bowed temp).symm
  change RG.flags (Pressure.temp (prism T s χ K (1:Config G c) (Greenbelt.allot i)).x)
    (prism T s χ K (1:Config G c) (Greenbelt.allot i)).V=∅ at hf
  unfold planted chamber
  rw [stored,hf,LocalLTE.Fan.Field.rosterD]

private theorem mean (fund:P.Funds S T) (Z:Coat T F):voltage Z.blank=0:=by
  have start:timeΛ Z 0=Z.blank:=by
    unfold timeΛ Vine.pass dry
    simp only [Prod.snd_zero,Work.G07.at_zero_increment]
    rfl
  exact start ▸ LocalLTE.Fan.volt0 Z fund

/-- At the flat held field the actual angular input and every root cutoff
are independent of the auxiliary Haar variable. -/
theorem fields (fund:P.Funds S T) (X:Coat T F) (flat:X.blank=X) (y:F.Slice G) (z:Air f G) (a:ℝ) (m:Wing) :
    field R X (y,z)=X.input (gStep R.beta • X.atmos z) ∧
    anchor R a m X (y,z)=X.enforce (2*a) (gStep R.beta • X.atmos z) (X.plaza (areas R T 0 X.B (m.badge S))):=by
  have sameY:(X.wrapY y).blank=X.wrapY y:=show X.blank.wrapY y=X.wrapY y from congrArg (fun Z:Coat T F=>Z.wrapY y) flat
  have zero:=mean fund (X.wrapY y)
  rw [sameY] at zero
  have step:worldZ (X.wrapY y) R.beta z=gStep R.beta • X.atmos z:=by rw [worldZ,zero,zero_add];rfl
  have actual:=WilsonHullGaussianMoment.entire_input X y (gStep R.beta • X.atmos z)
  rw [flat] at actual
  constructor
  · change (X.wrapY y).input (worldZ (X.wrapY y) R.beta z)=_
    rw [step];exact actual
  · change (X.wrapY y).enforce _ (worldZ (X.wrapY y) R.beta z) _=_
    rw [step];rfl

/-- The same original quadratic sampler at every admitted set of marked
heads, including previous forced insertions, with its quantitative fee. -/
theorem principal (prior:Team R) (H:Cash W s μ L Q o C T R) (temp:0≤Pressure.temp s) (χ:Chi)
    (i:Greenbelt.Reserve S) (tag:S.Choices) :
    let X:=((planted (prism T s χ o.K (1:Config G c) (Greenbelt.allot i)) (prior.signs S)).taggedL tag)
    ∀(p:Normal.poly (Eye X)) (d:ℕ),p.totalDegree≤d→
      ‖(∫z:Air f G,Cloud.paint (fun u=>z (tube X u)) p ∂X.dice)-
        Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T (Greenbelt.allot i) tag s)
          (WilsonOriginalSignedSamplerMoment.symmetry T (Greenbelt.allot i) tag s) 0 p‖≤
          Rise.coin p*WilsonOriginalSignedSamplerMoment.fee T L P o d s:=by
  rw [same prior χ s o.K temp i tag]
  exact WilsonOriginalSignedSamplerMoment.original T H temp χ ∅ i tag

end YM.Integration.WilsonPositionSeparatedProfileMayerFlat
