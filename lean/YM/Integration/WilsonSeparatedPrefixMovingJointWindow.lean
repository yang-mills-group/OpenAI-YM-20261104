import YM.Integration.WilsonSeparatedPrefixMovingJointSpectrum
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! An original absolute exterior window for the smooth separated joint test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointWindow
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open Metric
def plateau (a:Point4)(u v δ:ℝ)(hu:0≤u)(hv:0≤v)(hδ:0<δ):ContDiffBump a:=
  ⟨u+v+δ,u+v+2*δ,by positivity,by linarith⟩
def slot (a:Point4)(B:ContDiffBump a)(d:ℕ):Rarity d where
  ψ:=⟨B,B.contDiff⟩
  radius:=max 1 (B.rOut+‖a‖)
  markG:=le_max_left ..
  support:=by
    rw [B.tsupport_eq]
    intro z hz
    have he:=Metric.mem_closedBall.mp hz
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    have t:=norm_add_le (z-a) a
    rw [sub_add_cancel] at t
    exact (t.trans (add_le_add (by simpa only [dist_eq_norm] using he) le_rfl)).trans (le_max_right ..)
theorem original {d k:ℕ}(φ:Rarity d)(ψ:Rarity k)(a c:Point4)(u v δ gap:ℝ)
    (hu:0≤u)(hv:0≤v)(hδ:0<δ)(far:2*u+v+2*δ+gap≤‖c‖)
    (near:tsupport φ.ψ.val ⊆ closedBall a u)(outside:tsupport ψ.ψ.val ⊆ closedBall c v):
    let B:=plateau (a+c) u v δ hu hv hδ
    let χ:=slot (a+c) B k
    ContDiff ℝ ∞ χ.ψ.val ∧ ClearDay φ χ gap ∧
      ∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p)):=by
  intro B χ
  refine ⟨B.contDiff,?_,?_⟩
  · intro p hp q hq
    have narrow:=Metric.mem_closedBall.mp (near hp)
    change q∈tsupport (B:Point4→ℝ) at hq
    rw [B.tsupport_eq] at hq
    have wide:=Metric.mem_closedBall.mp hq
    have triangle:=dist_triangle a p (a+c)
    have triangle':=dist_triangle p q (a+c)
    rw [dist_comm a p] at triangle
    have distc:dist a (a+c)=‖c‖:=by rw [dist_eq_norm,show a-(a+c)=-c by abel,norm_neg]
    rw [distc] at triangle
    change dist q (a+c)≤u+v+2*δ at wide
    linarith
  intro p q
  by_cases n:φ.ψ.val p=0
  · simp [n]
  by_cases f:ψ.ψ.val (q-p)=0
  · simp [f]
  have hp:=Metric.mem_closedBall.mp (near (subset_closure n))
  have hq:=Metric.mem_closedBall.mp (outside (subset_closure f))
  have t:=norm_add_le (p-a) (q-p-c)
  rw [show p-a+(q-p-c)=q-(a+c) by abel] at t
  have mem:q∈closedBall (a+c) B.rIn:=by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm] at *
    change ‖q-(a+c)‖≤u+v+δ
    linarith
  have hχ:χ.ψ.val q=1:=B.one_of_mem_closedBall mem
  rw [hχ,one_mul]
end YM.Integration.WilsonSeparatedPrefixMovingJointWindow
