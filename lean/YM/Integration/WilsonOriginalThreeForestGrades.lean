import YM.Integration.WilsonOriginalThreeForestColors
import YM.Integration.WilsonOriginalForestSignedJet
import YM.Integration.WilsonOriginalPrimerCourseRead
/-! The joint forest coefficients read the registered individual sectors at their exact native degrees. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeForestGrades
open Function Finset Lattice RG Wilson Marker Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open Precision Tree WilsonOriginalPointCompactRoster WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonOriginalThreeCopiedCharts PhysicalForestAction PhysicalForestRay PhysicalForestMarkedRay
open Stationary Filter Matrix Next.SectorChange FreeResolvent MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open scoped Classical BigOperators ContDiff Topology
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {n N c:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (h:n.val∣N.val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "joint" => copyColor h M grades (fun a=>(M a).paint t) L tape
local notation "U" => bank owner grades sites T A h t L tape
local notation "own" i:max => (T (i)).rows (home sites (owner (i))) (alone A (owner (i)))

omit [Fintype I] in
theorem regular (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1) (legal:Legal tape L) (i:I):Bulk.Well ((U) i):=by
  let C:=T i
  let S:=home sites (owner i)
  let E:=alone A (owner i)
  have cap:∀v,‖WilsonOlderFreshGraphArmada.value E v‖≤1:=by intro v;exact bounded _ _ (v ()).property
  have staff:=WilsonOriginalPrimerCourseRead.salary S C.roll C.fare σ C.paid C.legal C.positive E cap
    (subject A (owner i) t) hs
  exact (copy_standard h (own i) (fun _=>grades (owner i)) (fun y=>((own i) y).paint (subject A (owner i) t))
    L tape staff legal).1

variable (S:StepData c N) (F:Forest S.ratio) {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (D:Matrix (Woods G N) (Woods G c) ℝ) (x:fieldDir G c 1) (z:Key F G→ℝ)
  (tag:S.Choices)(hD:D=reveal G S F*((reveal G S F).transpose*D))

include tag hD in
theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (legal:Legal tape L)(s:Hot (J)) (j:ℕ):
    readJet ((joint).power s+j) (chartMark S F D K x z (joint) s)=
      ∑i:I,if (J).fire (owner i)=s.val then charge i*readJet (((U) i).power name+j) (chartMark S F D K x z ((U) i) name) else 0:=by
  let f:I→ℝ→ℂ:=fun i=>chartMark S F D K x z ((U) i) name
  let a:I→ℂ:=fun i=>if (J).fire (owner i)=s.val then charge i else 0
  have ray:(chartMark S F D K x z (joint) s)=(fun g=>∑i,a i*f i g):=by
    funext g;rw [WilsonOriginalThreeForestColors.original owner grades sites T A charge h t L tape S F K D x z stock σpos hs bounded s]
    apply sum_congr rfl;intro i _;by_cases h:(J).fire (owner i)=s.val <;> simp [a,f,h]
  have smooth (i:I):ContDiffAt ℝ ∞ (f i) 0:=by
    have well:=regular owner grades sites T A h t L tape hs bounded legal i
    have raw:=((Bulk.geometric_ready K F tag ((U) i) well).2 name).1
    have path:ContDiffAt ℝ ∞ (fun g:ℝ=>g • Bulk.translated K F x z) 0:=contDiffAt_id.smul contDiffAt_const
    have atZero:ContDiffAt ℝ ∞ (Bulk.markFn S F ((U) i) name) ((0:ℝ) • Bulk.translated K F x z):=by
      rw [zero_smul];exact raw
    have moved:=atZero.comp 0 path
    exact moved.congr_of_eventuallyEq (PhysicalForestMarkedRay.marked S F D K x z tag ((U) i) name hD).symm
  rw [ray,WilsonOriginalForestSignedJet.roster _ f a (fun i=>(smooth i).of_le (by exact_mod_cast (le_top : ((joint).power s+j:ℕ∞)≤⊤)))]
  apply sum_congr rfl;intro i _
  by_cases hit:(J).fire (owner i)=s.val
  · have power:(joint).power s=((U) i).power name:=by
      change Launch.index (J) grades s.val+1=Launch.index (Stock.census Unit) (fun _=>grades (owner i)) name.val+1
      rw [←hit]
      simp [Launch.index,Stock.census,Marker.Census.fire,name]
    simp [a,f,hit,power]
  · simp [a,hit]

end YM.Integration.WilsonOriginalThreeForestGrades
