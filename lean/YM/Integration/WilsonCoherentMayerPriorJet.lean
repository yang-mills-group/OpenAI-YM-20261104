import YM.Integration.WilsonCoherentMayerPriorDifferential

/-! Numerical Taylor approximation of the actual entire coupling stratum by its own radial jet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorJet
open Lattice Wilson RG Marker LocalComparison NativePaidPacketGroups
open WilsonCoherentMayerPriorDifferential WilsonCoherentMayerPriorRay
open WilsonCoherentMayerPriorStratum WilsonCoherentMayerPriorAtom WilsonMeasuredPathTaylor
open scoped Classical BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

include H in
theorem purchased (hg:g≠0)(s:Γ.Mode)(hs:s.val.Nonempty)(z:ℤ)
    (x:IndependentTests D)(a:Directions G n){A:ℝ}(ha:0≤A)(available:∀e,speed a e≤A)(q:ℕ)(t:ℝ):
    let f:=reading P s z (testInclusion D x) a
    ‖f t-jet f q t‖≤fee width A q t*(bank/weight w g s z):=by
  intro f
  let F (i:Fiber P s z):=curve (token P s z i) (testInclusion D x) a
  let b:=fee width A q t
  have hb:0≤b:=by dsimp only [b,fee];have hw:=H.width_pos;positivity
  have cash:=paid H hg s hs z
  have jets:HasSum (fun i=>jet (F i) q t) (jet f q t):=hasSum_sum (s:=Finset.range (q+1))
    (fun k _=>(WilsonCoherentMayerPriorDifferential.issued H hg s hs z x a ha available k 0).const_smul _)
  have raw:HasSum (fun i=>F i t) (f t):=(NativePaidPacketSeries.value_summable H hg s
    (fun he=>Finset.nonempty_iff_ne_empty.mp hs (by rw [he];rfl)) z (testInclusion D x) (field a t)).hasSum
  have each (i:Fiber P s z):‖F i t-jet (F i) q t‖≤b*rent width i:=by
    have h:=WilsonMeasuredPathTaylor.remainder (WilsonCoherentMayerPriorRay.smooth (token P s z i)
      (testInclusion D x) a) q t (rent width i*wage width A (q+1))
      (fun u=>WilsonCoherentMayerPriorRay.bounded H (token_eq P s z i) x a ha available (q+1) u)
    refine h.trans_eq ?_
    dsimp only [wage,b,fee]
    have hw:=H.width_pos.ne'
    have hn:(↑(q+1).factorial:ℝ)≠0:=by positivity
    rw [show 2*A*|t|/width=(2*A/width)*|t| by ring,mul_pow]
    field_simp
  have bounded:=Summable.of_nonneg_of_le (fun i=>norm_nonneg (F i t-jet (F i) q t)) each (cash.2.1.mul_left b)
  rw [←(raw.sub jets).tsum_eq]
  apply (norm_tsum_le_tsum_norm bounded).trans ((bounded.tsum_le_tsum each (cash.2.1.mul_left b)).trans ?_)
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left cash.2.2 hb

end YM.Integration.WilsonCoherentMayerPriorJet
