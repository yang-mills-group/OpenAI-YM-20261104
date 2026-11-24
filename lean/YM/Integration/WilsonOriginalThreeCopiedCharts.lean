import YM.Integration.WilsonOriginalThreeCopiedWords
import YM.Integration.WilsonOriginalPrimerForestRead

/-! The common original color and all of its separately financed unit colors along the actual nonlinear forest chart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeCopiedCharts
open Function Finset Lattice RG Wilson Marker Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6
open Precision Tree WilsonOriginalPointCompactRoster WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonOriginalThreeCopiedWords WilsonOriginalPinnedGradedPeek PhysicalForestRay PhysicalForestMarkedRay
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (h:n.val∣N.val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "own" i:max => (T (i)).rows (home sites (owner (i))) (alone A (owner (i)))
local notation "test" i:max => subject A (owner (i)) t

abbrev bank (i:I):=copyColor h (own i) (fun _=>grades (owner i)) (fun y=>((own i) y).paint (test i)) L tape
def name:Hot (Stock.census Unit):=⟨(Stock.census Unit).fire (),singleton_nonempty ()⟩

omit [Fintype I] in
theorem solo_mark (bounded:∀v a,a∈A v→‖a‖≤1) (hs:0<σ) (i:I) (z:Joint G N):
    solo owner grades sites T A h t i z=(bank owner grades sites T A h t L tape i).mark name z.1 (RG.increment 1 z.2):=by
  have stock:Scene.Armada (own i) (fun _=>1) (fun _=>grades (owner i)) σ (1+(T i).cost (home sites (owner i))) q 1 (grades (owner i)):=by
    have c:=budget_nonneg (WilsonOriginalPointCompactSalary.original_salary owner grades sites T A i hs.le)
    apply (T i).earnings (home sites (owner i)) (alone A (owner i)) hs.le _
    · exact zero_lt_one
    · linarith
    · simp
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · intro v;exact bounded _ _ (v ()).property
  have sel:(fun _:(T i).Roster=>fun _:PagesOf n N=>True)=(fun y=>fun _=>((own i) y).mode=name.val):=by
    funext y p;exact propext (iff_true_intro (show ((own i) y).mode=name.val from rfl)).symm
  unfold solo
  rw [sel]
  exact WilsonOriginalOccupiedFieldLayout.filed h (own i) (test i) stock hs L tape name z

theorem held {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (s:Hot (J)) (z:Joint G N):
    (copyColor h M grades (fun a=>(M a).paint t) L tape).mark s z.1 (RG.increment 1 z.2)=
      ∑i:I,if (J).fire (owner i)=s.val then charge i*(bank owner grades sites T A h t L tape i).mark name z.1 (RG.increment 1 z.2) else 0:=by
  rw [WilsonOriginalThreeCopiedWords.filed owner grades sites T A charge h t stock σpos s L tape z]
  simp_rw [solo_mark owner grades sites T A h t L tape bounded hs]

end YM.Integration.WilsonOriginalThreeCopiedCharts
