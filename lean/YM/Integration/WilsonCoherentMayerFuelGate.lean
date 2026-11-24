import YM.Integration.WilsonCoherentMayerFuelPolynomial
import YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety

/-! The two actual endpoints of the original covariance correction buy one Gaussian warning. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelGate
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


open LocalTaylorR2.Exponent WilsonCoherentMayerFuelPolynomial
variable (X:Coat T F)

def sites (q:Ledger f 2):Support c:={atEdge S q.2.1,atEdge S (arrive q.2.1 q.2.2)}

theorem count (q:Ledger f 2):(sites (S:=S) q).card≤2:=by
  unfold sites;exact (Finset.card_insert_le _ _).trans (by simp)

theorem cleared (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (Y:Support c) (e:Bond f) (he:atEdge S e∈Y) (z:Air f G) (quiet:z∉eerie X Y o.ξ R.beta):
    X.aperture R.beta z o.a e=1 := by
  unfold Coat.aperture
  split
  next exposed =>
    have info:=H.laws.data
    have temp:0<X.t:=info.room.fiery
    have lower:=info.safety.2.2.2 F X rfl fitted manifest
    have watching:X.watch (atEdge S e) o.ξ R.beta X.B z:=by
      intro t ht;exact atHome X Y o.ξ R.beta z quiet _ he t (by omega)
    have bounded:‖(X.liftA R.beta z) e‖≤o.a*X.t:=by
      have h:=(X.watch_bonds (atEdge S e) temp o.rare.le H.laws.intake.positive watching e
        (by rw [separation_self];omega) (lower.1 e)).2
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith [info.safety.2.2.1,info.safety.2.1]) temp.le)
    by_contra missed
    have cut:=X.χ.exterior_gt ‖(X.liftA R.beta z) e‖ ((2*o.a)*X.t) (norm_nonneg _)
      (by have h:=o.large;positivity) (sub_ne_zero.mpr (Ne.symm missed))
    nlinarith [mul_pos o.large temp]
  next => rfl

def weight (q:Ledger f 2) (β a:ℝ) (k:ℕ) (z:Air f G) :=
  (X.aperture β z a q.2.1 * X.aperture β z a (arrive q.2.1 q.2.2))^k

theorem range (q:Ledger f 2) (β a:ℝ) (k:ℕ) (z:Air f G):weight X q β a k z∈Set.Icc 0 1:=by
  have hit (e:Bond f):X.aperture β z a e∈Set.Icc 0 1:=by
    unfold Coat.aperture;split
    next => exact X.booked _ _ _
    next => simp
  have non:=mul_nonneg (hit q.2.1).1 (hit (arrive q.2.1 q.2.2)).1
  have bound: X.aperture β z a q.2.1 * X.aperture β z a (arrive q.2.1 q.2.2)≤1:=
    (mul_le_mul (hit _).2 (hit _).2 (hit _).1 zero_le_one).trans_eq (one_mul _)
  exact ⟨pow_nonneg non k,pow_le_one₀ non bound⟩

theorem live (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (q:Ledger f 2) (k:ℕ) (z:Air f G) (quiet:z∉eerie X (sites (S:=S) q) o.ξ R.beta) :
    weight X q R.beta o.a k z=1 := by
  unfold weight
  rw [cleared X H fitted manifest _ _ (by simp [sites]) z quiet,
    cleared X H fitted manifest _ _ (by simp [sites]) z quiet,one_mul,one_pow]

theorem measured (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (q:Ledger f 2) (k:ℕ) :
    {z:Air f G | weight X q R.beta o.a k z≠1}⊆eerie X (sites (S:=S) q) o.ξ R.beta := by
  intro z hz;by_contra quiet;exact hz (live X H fitted manifest q k z quiet)

end YM.Integration.WilsonCoherentMayerFuelGate
