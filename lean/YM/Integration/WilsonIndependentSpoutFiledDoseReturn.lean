import YM.Integration.WilsonIndependentSpoutDoseBoundary

/-! One original return for all terms in a filed product, with its measured thermal factors in the opening chart. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFiledDoseReturn
open Finset PowerSeries Lattice Wilson RG Precision PertExtension WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutDoseBoundary (into)
open scoped Classical BigOperators
variable {G:Gauge}{T:Type}[Fintype T]

theorem sum (Z:T → Era G ℝ):ground (∑t,Z t)=∑t,ground (Z t):=by
  ext q
  have terms:(∑t,Z t).2=∑t,(Z t).2:=map_sum (AddMonoidHom.snd _ _) Z univ
  simp only [ground,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk,map_sum,terms,Finset.sum_apply]

theorem original (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (N k b m:ℕ)(mb:m ≤ b)(bn:b ≤ N)(h:T → ℕ)(cut:∀t,h t ≤ k)
    (F:Era G ℝ)(X Q:T → Era G ℝ)(fee:T → Cost)(actual:F=∑t,X t)
    (funded:∀t,Auth (h t) (X t))(base:∀t,Auth (h t) (Q t))
    (filed:∀t n,(X t).1 n=affix (fee t) ((Q t).1 n)):
    WilsonIndependentSpoutDoseBoundary.measure A O N k b m F=∑t,into A O N b (fee t)*WilsonIndependentSpoutDoseBoundary.measure A O N (h t) b m (Q t):=by
  rw [actual,WilsonIndependentSpoutDoseBoundary.measure,WilsonIndependentSpoutDoseBoundary.checkedSum A O simple valid N b m k mb bn X
    (fun t=>(funded t).tall (cut t)),sum,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  change WilsonIndependentSpoutDoseBoundary.measure A O N k b m (X t)=_
  rw [WilsonIndependentSpoutDoseBoundary.earned A O simple valid N k b m mb bn (X t) (Q t) (fee t)
    ((funded t).tall (cut t)) ((base t).tall (cut t)) (filed t)]
  unfold WilsonIndependentSpoutDoseBoundary.measure
  rw [WilsonIndependentSpoutDoseBoundary.cap A O simple valid N b m (h t) k mb bn (cut t) (Q t) (base t)]

theorem opening (A:Levels G)(O:ChartRatio G)(N:ℕ)(c:Cost):into A O N N c=c:=by
  simp [WilsonIndependentSpoutDoseBoundary.into,relativeC,leeB]

end YM.Integration.WilsonIndependentSpoutFiledDoseReturn
