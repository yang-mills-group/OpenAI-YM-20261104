import YM.Integration.WilsonSeparatedPrefixCanonicalConvolution
import YM.Integration.WilsonSeparatedPrefixCanonicalClearHeard

/-! Carry the complete singleton scalar factors through a genuinely varying original receiver. -/
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution
open Function Finset Set MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums RG12
open Extra.Histories Extra.Histories.Relay Extra.Multi Extra.Trajectories Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many PhysicalNext.Repeat.Legato
open WilsonThermometerCorridorFiling WilsonThermometerCorridorRoster WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f u:ℕ}{V V':Type}[DecidableEq V][DecidableEq V']{J:Census V}{K:Census V'}
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "Field" => Config G ((C).side f p)
open WilsonSeparatedPrefixCanonicalClearHeard

def readingAt (F:Field→ℂ)(uf:u≤f)(U:Config G ((C).side u p)):ℂ:=
  (((C).path.rep N p u).eval U:ℂ)⁻¹*gust (C).path N p f F u uf U

theorem coordinate (F:Field→Poly J)(paid:Integrable F (prior G _))(s:J.Mode)(uf:u≤f)(W:Config G ((C).side u p)):
    (WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F uf W).part s=readingAt R (N:=N) (fun U=>(F U).part s) uf W:=by
  change _*(gust (C).path N p f F u uf W).part s=_*gust (C).path N p f _ u uf W
  rw [congrFun (projected R F paid s uf) W]

omit R in
private theorem pushed {n m:Side}{S:StepData m n}{F:Config G n→Poly J}{x:ℝ}
    (h:S.IsKernel x G)(live:Integrable F (prior G _))(L:Poly J →L[ℂ] Poly K):
    (fun U=>L (S.push x F U))=S.push x (fun U=>L (F U)):=by
  let D:=L.restrictScalars ℝ
  funext U
  unfold StepData.push
  have eq:=D.integral_comp_comm (StepData.push_slice h U F live)
  simp_rw [D.map_smul] at eq
  exact eq.symm

theorem transformed (L:Poly J →L[ℂ] Poly K)(F:Field→Poly J)(paid:Integrable F (prior G _))(uf:u≤f)(W:Config G ((C).side u p)):
    L (WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F uf W)=WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) (fun U=>L (F U)) uf W:=by
  have transit:(fun U=>L (gust (C).path N p f F u uf U))=
      gust (C).path N p f (fun U=> L (F U)) u uf:=by
    clear W
    induction uf using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ j jt ih=>
      rw [gust_step (C).path N p f F jt,gust_step (C).path N p f _ jt]
      exact (pushed ((A).transition_mass j p ((C).path.β N p (j+1)))
        (gust_live (C).path N p f F paid jt) L).trans
        (congrArg (((A).clock.op j p).push ((C).path.β N p (j+1))) ih)
  unfold WilsonSeparatedPrefixCanonicalClearHeard.held
  rw [L.map_smul,congrFun transit W]

end YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Labels Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Marker MergeProof MergeProof.Accent
open Extra.Histories Ac Push GridApprox.Nil Extra.Multi Extra.Trajectories Lodestar
open WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V][Fintype V]{N p f u:ℕ}
local notation "S₀" => (Marks V)
local notation "S₂" => (Marks (V×Bool))
local notation "Field" => Config G (R.family.side f p)

theorem original (w:V → ℝ)(wp:∀i,0<w i)(C:Poly S₀)
    (F₁ F₀:Field → Poly S₂)(g₁ g₀:Field → ℂ)(s:(S₀).Mode)
    (live₁:Integrable F₁ (prior G _))(live₀:Integrable F₀ (prior G _))
    (high:∀U,g₁ U=(duplicate V C*F₁ U).part (two s))
    (low:∀U,g₀ U=(duplicate V C*F₀ U).part (two s))
    (stop:u≤f)(endpoint:Config G (R.family.side u p))(fee:(S₂).Mode → ℝ)
    (paid:∀t,‖(WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₁ stop endpoint).part t-(WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₀ stop endpoint).part t‖≤fee t):
    Poly.toll (fun i=>w i^2) s*‖readingAt R (N:=N) g₁ stop endpoint-readingAt R (N:=N) g₀ stop endpoint‖≤
      Poly.price (fun i=>w i^2) C*(∑t,Poly.toll (w ∘ Prod.fst) t*fee t) := by
  let W:V×Bool → ℝ:=w ∘ Prod.fst
  have pos(i):0<W i:=wp i.1
  let L:Poly S₂ →L[ℂ] Poly S₂:=LinearMap.toContinuousLinearMap (Algebra.lmul ℂ (Poly S₂) (duplicate V C))
  have view (F:Field → Poly S₂)(alive:Integrable F (prior G _))(g:Field → ℂ)
      (same:∀U,g U=(duplicate V C*F U).part (two s)):
      readingAt R (N:=N) g stop endpoint=(duplicate V C*WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F stop endpoint).part (two s):=by
    rw [funext same]
    change readingAt R (N:=N) (fun U=>(L (F U)).part (two s)) stop endpoint=(L (WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F stop endpoint)).part (two s)
    rw [transformed R L F alive stop endpoint,coordinate R _ (L.integrable_comp alive) (two s) stop endpoint]
  let Y:=WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₁ stop endpoint-WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₀ stop endpoint
  have net:Poly.price W Y≤∑t,Poly.toll W t*fee t:=Finset.sum_le_sum (fun t _=>
    mul_le_mul_of_nonneg_left (paid t) (Poly.worth pos t).le)
  rw [view F₁ live₁ g₁ high,view F₀ live₀ g₀ low,←two_toll,←WilsonSeparatedPrefixCanonicalConvolution.duplicated]
  change Poly.toll W (two s)*‖((duplicate V C*WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₁ stop endpoint)-
      (duplicate V C*WilsonSeparatedPrefixCanonicalClearHeard.held R (N:=N) F₀ stop endpoint)).part (two s)‖≤_
  rw [←mul_sub]
  exact (Poly.member pos _ _).trans ((Poly.multiplication pos _ Y).trans
    (mul_le_mul_of_nonneg_left net (Poly.nonnegative pos _)))

end YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution
end
