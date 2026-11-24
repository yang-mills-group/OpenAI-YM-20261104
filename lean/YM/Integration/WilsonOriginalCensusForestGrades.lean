import YM.Integration.WilsonOriginalCensusCopySlate
import YM.Integration.WilsonOriginalThreeForestGrades

/-! The entered mixed census on the real nonlinear forest chart, differentiated only after
each connected child has been assigned its native total suspension degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusForestGrades
open Function Finset Lattice RG Wilson Marker Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open Precision Tree WilsonOriginalPointCompactRoster WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonOriginalThreeCopiedCharts PhysicalForestAction PhysicalForestRay PhysicalForestMarkedRay
open Stationary Filter Matrix Next.SectorChange FreeResolvent MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open scoped Classical BigOperators ContDiff Topology
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n N c:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(B:I→Binder P (Stock.census V))(grades:V→ℕ)
  {q:ℕ}{σ:ℝ}(T:∀i,Copy G (∑v∈(B i).mode.val,grades v) q σ)
  (div:n.val∣N.val)(x:Wallet (room V))(π:Layout G)(tape:Finset Age)
local notation "own" i:max => (T (i)).rows (WilsonOlderFreshGraphPointWallet.point (B (i)).center) disk
local notation "M" => mounted B (fun i=>own i)
local notation "J" => Stock.census V

local notation "joint" => copyColor div M grades (fun a=>(M a).paint x) π tape
local notation "U" => color B grades T div x π tape

private theorem angular (u:Link G N):mantle u=RG.increment 1 (edgeColor u):=by
  rw [←Mosaic.mantle_input]
  funext e
  change input G N u e=G.lieExp (edgeColor u e)*1
  rw [input_color,mul_one]

omit [Fintype I] in
theorem regular (hs:0<σ)(legal:Legal tape π)(i:I):Bulk.Well ((U) i):=by
  let P₁:=WilsonOlderFreshGraphPointWallet.point (B i).center
  have cap:∀v,‖WilsonOlderFreshGraphArmada.value disk v‖≤1:=fun v=>(v ()).property
  have staff:=WilsonOriginalPrimerCourseRead.salary P₁ (T i).roll (T i).fare σ (T i).paid
    (T i).legal (T i).positive disk cap (project (B i).mode x) hs
  exact (copy_standard div (own i) (fun _=>∑v∈(B i).mode.val,grades v) (fun z=>((own i) z).paint
    (project (B i).mode x)) π tape staff legal).1

variable (S:StepData c N)(F:Forest S.ratio){p:Clip}{path:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p path O)(D:Matrix (Woods G N) (Woods G c) ℝ)(v:fieldDir G c 1)(z:Key F G→ℝ)
theorem on_forest {w:V→ℝ}{σ₀ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C order seats shelf)(width:0<σ₀)(hs:0<σ)(s:Hot (J))(g:ℝ):
    chartMark S F D K v z (joint) s g=
      ∑i:I,if (B i).mode=s.val then chartMark S F D K v z ((U) i) name g else 0:=by
  simp only [chartMark,PhysicalForestAction.field,angular]
  exact WilsonOriginalCensusCopySlate.filed B grades T div x π tape stock width hs s (g,_)

theorem original {w:V→ℝ}{σ₀ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C order seats shelf)(width:0<σ₀)(hs:0<σ)
    (legal:Legal tape π)(tag:S.Choices)(sweep:D=reveal G S F*((reveal G S F).transpose*D))
    (s:Hot (J))(j:ℕ):
    readJet ((joint).power s+j) (chartMark S F D K v z (joint) s)=
    ∑i:I,if (B i).mode=s.val then readJet (((U) i).power name+j) (chartMark S F D K v z ((U) i) name) else 0:=by
  let f:I→ℝ→ℂ:=fun i=>chartMark S F D K v z ((U) i) name
  let a:I→ℂ:=fun i=>if (B i).mode=s.val then 1 else 0
  have ray:(chartMark S F D K v z (joint) s)=(fun g=>∑i,a i*f i g):=by
    funext g
    rw [on_forest B grades T div x π tape S F K D v z stock width hs s]
    apply sum_congr rfl;intro i _
    by_cases hit:(B i).mode=s.val <;> simp [a,f,hit]
  have smooth (i:I):ContDiffAt ℝ ∞ (f i) 0:=by
    have well:=regular B grades T div x π tape hs legal i
    have raw:=((Bulk.geometric_ready K F tag ((U) i) well).2 name).1
    have path₀:ContDiffAt ℝ ∞ (fun g:ℝ=>g • Bulk.translated K F v z) 0:=contDiffAt_id.smul contDiffAt_const
    have atZero:ContDiffAt ℝ ∞ (Bulk.markFn S F ((U) i) name) ((0:ℝ) • Bulk.translated K F v z):=by
      rw [zero_smul];exact raw
    exact (atZero.comp 0 path₀).congr_of_eventuallyEq (PhysicalForestMarkedRay.marked S F D K v z tag ((U) i) name sweep).symm
  rw [ray,WilsonOriginalForestSignedJet.roster _ f a (fun i=>(smooth i).of_le (by exact_mod_cast (le_top : ((joint).power s+j:ℕ∞)≤⊤)))]
  apply sum_congr rfl;intro i _
  by_cases hit:(B i).mode=s.val
  · have power:(joint).power s=((U) i).power name:=by
      change Launch.index (J) grades s.val+1=Launch.index (Stock.census Unit) (fun _=>∑v∈(B i).mode.val,grades v) name.val+1
      rw [←hit]
      simp [Launch.index,Stock.census,Marker.Census.fire,name]
    simp [a,f,hit,power]
  · simp [a,hit]

end YM.Integration.WilsonOriginalCensusForestGrades
end
