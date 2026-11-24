import YM.Integration.WilsonCoherentMayerFuelPolynomial

/-! The complete marked Wick book with a genuine repeated covariance occurrence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelWick
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


open WilsonCoherentMayerFuelPolynomial
variable (X:Coat T F) (q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks)

def word (k:ℕ) (B:Normal.poly (Eye X)) :=
  MvPolynomial.C (((k.factorial:ℝ)⁻¹):ℂ) * quadratic X q first last ^ k * B

theorem degree (k D:ℕ) (B:Normal.poly (Eye X)) (hb:B.totalDegree≤D) :
    (word X q first last k B).totalDegree≤2*k+D := by
  unfold word
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add _ hb
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have h:=WilsonCoherentMayerFuelPolynomial.degree X q first last
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h

theorem printed (k:ℕ) (B:Normal.poly (Eye X)) (z:Air f G) :
    Cloud.paint (fun i=>z (tube X i)) (word X q first last k B)=
      (((X.qunique z q)^k/k.factorial:ℝ):ℂ) * Cloud.paint (fun i=>z (tube X i)) B := by
  rw [word,map_mul,map_mul,map_pow,read_quadratic]
  have scalar:Cloud.paint (fun i=>z (tube X i))
      (MvPolynomial.C (((k.factorial:ℝ)⁻¹):ℂ))=(((k.factorial:ℝ)⁻¹):ℂ):=by simp [Cloud.paint]
  rw [scalar]
  push_cast
  ring

theorem incidence (H:Cash W s μ L Q o C T R) (k:ℕ) (B:Normal.poly (Eye X)) (z:Air f G) :
    (((Mayer.exponent H X z (label (S:=S) q))^k/k.factorial:ℝ):ℂ) *
        Cloud.paint (fun i=>z (tube X i)) B =
      ((X.aperture R.beta z o.a q.2.1 * X.aperture R.beta z o.a (arrive q.2.1 q.2.2))^k:ℝ) *
        Cloud.paint (fun i=>z (tube X i)) (word X q first last k B) := by
  rw [printed]
  change (((X.chain R.beta z o.a q)^k/k.factorial:ℝ):ℂ)*_ = _
  simp only [Coat.chain,mul_pow]
  push_cast
  ring

variable (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (loc:I→Site f)
    (phase:I→Reading) (θ:ℝ) (y:(i:I)→ run.family.label (d i))

/-- Only the original non-common inverse rate is spent on this complete polynomial. -/
theorem measured (H:Cash W s μ L Q o C T R) (temp:0≤Pressure.temp s) (χ:Chi) (i:Greenbelt.Reserve S)
    (tag:S.Choices) (g:ℝ) (p:ℕ) (v:Ledger f 2) (a:v.2.1∉(Greenbelt.allot i).trunks)
    (b:arrive v.2.1 v.2.2∉(Greenbelt.allot i).trunks) (k:ℕ):
    let X:=chamber T s o.K χ 1 ∅ i tag
    let B:=WilsonPositionSeparatedProfileMayerWickWord.book X run d loc phase θ y g p
    let packet:=word X v a b k B
    ‖(∫ z:Air f G, (((X.qunique z v)^k/k.factorial *
        WilsonCoherentMayerSignedCharge.polynomial run d (F:=Greenbelt.allot i) loc phase θ g y p z:ℝ):ℂ) ∂X.dice) -
      Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T (Greenbelt.allot i) tag s)
        (WilsonOriginalSignedSamplerMoment.symmetry T (Greenbelt.allot i) tag s) 0 packet‖ ≤
      Rise.coin packet*WilsonOriginalSignedSamplerMoment.fee T L P o (2*k+p) s := by
  intro X B packet
  have bound:=degree X v a b k p B (WilsonPositionSeparatedProfileMayerWickWord.degree X run d loc phase θ y g p)
  have paid:=WilsonOriginalSignedSamplerMoment.original T H temp χ ∅ i tag packet (2*k+p) bound
  have same:(∫ z:Air f G,(((X.qunique z v)^k/k.factorial *
      WilsonCoherentMayerSignedCharge.polynomial run d (F:=Greenbelt.allot i) loc phase θ g y p z:ℝ):ℂ) ∂X.dice)=
      ∫ z:Air f G,Cloud.paint (fun h=>z (tube X h)) packet ∂X.dice := by
    apply integral_congr_ae;filter_upwards with z
    rw [printed,WilsonPositionSeparatedProfileMayerWickWord.printed,Complex.ofReal_mul]
  rw [same]
  exact paid

end YM.Integration.WilsonCoherentMayerFuelWick
