import YM.Integration.WilsonCoherentMayerPriorRay

/-! Absolute differentiation of the entire occupied coupling stratum on the original angular ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorDifferential
open Lattice Wilson RG Marker LocalComparison NativePaidPacketGroups
open WilsonCoherentMayerPriorRay WilsonCoherentMayerPriorStratum WilsonMeasuredPathTaylor
open scoped Classical BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

def reading (P:MarkedPackets D G n Γ)(s:Γ.Mode)(z:ℤ)(x:TestSpace D)(a:Directions G n)(t:ℝ):ℂ:=
  NativePaidPacketSeries.value P s z x (field a t)

include H in
theorem issued (hg:g≠0)(s:Γ.Mode)(hs:s.val.Nonempty)(z:ℤ)
    (x:IndependentTests D)(a:Directions G n){A:ℝ}(ha:0≤A)(available:∀e,speed a e≤A)(k:ℕ)(t:ℝ):
    HasSum (fun i:Fiber P s z=>iteratedDeriv k (curve (token P s z i) (testInclusion D x) a) t)
      (iteratedDeriv k (reading P s z (testInclusion D x) a) t):=by
  let F (i:Fiber P s z):=curve (token P s z i) (testInclusion D x) a
  let B (r:ℕ) (i:Fiber P s z):=rent width i*wage width A r
  have cash:=paid H hg s hs z
  have regular (i:Fiber P s z):ContDiff ℝ ω (F i):=WilsonCoherentMayerPriorRay.smooth .. 
  have summable (r:ℕ):Summable (B r):=cash.2.1.mul_right _
  have control (r:ℕ) (i:Fiber P s z) (u:ℝ):‖iteratedFDeriv ℝ r (F i) u‖≤B r i:=by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact WilsonCoherentMayerPriorRay.bounded H (token_eq P s z i) x a ha available r u
  change HasSum (fun i=>iteratedDeriv k (F i) t) (iteratedDeriv k (fun u=>∑'i,F i u) t)
  rw [iteratedDeriv_eq_iteratedFDeriv,iteratedFDeriv_tsum_apply (f:=F) (k:=k) (N:=(k:ℕ∞))
    (fun i=>(regular i).of_le (by simp)) (fun r _=>summable r) (fun r i u _=>control r i u) le_rfl]
  let v:=fun _:Fin k=>(1:ℝ)
  have allDerivatives:Summable (fun i=>iteratedFDeriv ℝ k (F i) t):=
    Summable.of_norm_bounded (summable k) (fun i=>control k i t)
  change HasSum _ ((∑'i,iteratedFDeriv ℝ k (F i) t) v)
  exact allDerivatives.hasSum.map (ContinuousMultilinearMap.apply ℝ _ _ v).toAddMonoidHom
    (ContinuousMultilinearMap.apply ℝ _ _ v).continuous

end YM.Integration.WilsonCoherentMayerPriorDifferential
