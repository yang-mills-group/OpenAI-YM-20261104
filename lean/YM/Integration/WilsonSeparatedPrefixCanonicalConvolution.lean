import YM.Integration.WilsonSeparatedPrefixCanonicalDifference
import YM.Integration.WilsonSeparatedPrefixCanonicalHeard

/-! Return the global occupied scalar factors on each original output mode, using one
genuine normalization at the same old flat. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalConvolution
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Labels Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Marker MergeProof MergeProof.Accent
open Extra.Histories Ac Push GridApprox.Nil Extra.Multi Extra.Trajectories Lodestar
open WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V][Fintype V]{N p f u:ℕ}
local notation "S₀" => (Marks V)
local notation "S₂" => (Marks (V×Bool))
local notation "Field" => Config G (R.family.side f p)

theorem duplicated (w:V → ℝ)(C:Poly S₀):
    Poly.price (w ∘ Prod.fst) (duplicate V C)=Poly.price (fun i=>w i^2) C:=by
  let d:Sheet S₀:=fun s=>‖C.part s‖
  have eq:∀t,‖(duplicate V C).part t‖=transfer d t:=by
    intro t
    by_cases h:∃s,t=two s
    · obtain ⟨s,rfl⟩:=h
      rw [seal_part,at_two]
    · rw [transfer_miss d t (fun i e=>h ⟨i,e⟩),seal_miss C t (fun i e=>h ⟨i,e⟩),norm_zero]
  change (∑t,Poly.toll (w ∘ Prod.fst) t*‖(duplicate V C).part t‖)=_
  simp_rw [eq]
  exact price_transfer w d

theorem original (w:V → ℝ)(wp:∀i,0<w i)(C:Poly S₀)
    (F₁ F₀:Field → Poly S₂)(g₁ g₀:Field → ℂ)(s:(S₀).Mode)
    (live₁:Integrable F₁ (prior G _))(live₀:Integrable F₀ (prior G _))
    (high:∀U,g₁ U=(duplicate V C*F₁ U).part (two s))
    (low:∀U,g₀ U=(duplicate V C*F₀ U).part (two s))
    (stop:u≤f)(fee:(S₂).Mode → ℝ)
    (paid:∀t,‖(amount R (N:=N) F₁ stop).part t-(amount R (N:=N) F₀ stop).part t‖≤fee t):
    Poly.toll (fun i=>w i^2) s*‖reading R (N:=N) g₁ u stop-reading R (N:=N) g₀ u stop‖≤
      Poly.price (fun i=>w i^2) C*(∑t,Poly.toll (w ∘ Prod.fst) t*fee t) := by
  let W:V×Bool → ℝ:=w ∘ Prod.fst
  have pos(i):0<W i:=wp i.1
  let L:Poly S₂ →L[ℂ] Poly S₂:=LinearMap.toContinuousLinearMap (Algebra.lmul ℂ (Poly S₂) (duplicate V C))
  have view (F:Field → Poly S₂)(alive:Integrable F (prior G _))(g:Field → ℂ)
      (same:∀U,g U=(duplicate V C*F U).part (two s)):
      reading R (N:=N) g u stop=(duplicate V C*amount R (N:=N) F stop).part (two s):=by
    rw [funext same]
    change reading R (N:=N) (fun U=>(L (F U)).part (two s)) u stop=(L (amount R (N:=N) F stop)).part (two s)
    rw [transformed R L F alive stop,coordinate R _ (L.integrable_comp alive) (two s)]
  let Y:=amount R (N:=N) F₁ stop-amount R (N:=N) F₀ stop
  have net:Poly.price W Y≤∑t,Poly.toll W t*fee t:=Finset.sum_le_sum (fun t _=>
    mul_le_mul_of_nonneg_left (paid t) (Poly.worth pos t).le)
  rw [view F₁ live₁ g₁ high,view F₀ live₀ g₀ low,←two_toll,←duplicated]
  change Poly.toll W (two s)*‖((duplicate V C*amount R (N:=N) F₁ stop)-
      (duplicate V C*amount R (N:=N) F₀ stop)).part (two s)‖≤_
  rw [←mul_sub]
  exact (Poly.member pos _ _).trans ((Poly.multiplication pos _ Y).trans
    (mul_le_mul_of_nonneg_left net (Poly.nonnegative pos _)))

end YM.Integration.WilsonSeparatedPrefixCanonicalConvolution
end
