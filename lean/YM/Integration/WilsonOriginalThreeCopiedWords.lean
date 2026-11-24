import YM.Integration.WilsonOriginalPointCompactFaces
import YM.Integration.WilsonOriginalPinnedGradedPeek

/-! At the actual upper group field, copying the three-color roster preserves each original charged unit and each separately stationed unary source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeCopiedWords
open Function Finset Lattice RG Wilson Marker Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPointCompactRoster WilsonOriginalPaidWalkCover WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (h:n.val∣N.val) (t:Wallet A)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "own" i:max => (T (i)).rows (home sites (owner (i))) (alone A (owner (i)))
local notation "test" i:max => subject A (owner (i)) t

omit [Fintype I] in
theorem letter (i:I) (y:(T i).Roster) (p:PagesOf n N) (z:Joint G N):
    token h M t ⟨i,y⟩ p z=charge i*token h (own i) (test i) y p z:=by
  unfold token
  rw [centered,centered]
  exact mul_assoc _ _ _

def solo (i:I) (z:Joint G N):ℂ:= frame h (own i) (test i) (fun _ _=>True) z

theorem collected {w:Fin 3→ℝ} {σ₀ C:ℝ} {d seats shelf:ℕ} (stock:Scene.Armada M w grades σ₀ C d seats shelf)
    (σpos:0<σ₀) (s:(J).Mode) (z:Joint G N):
    frame h M t (fun i _=>(M i).mode=s) z =
      ∑i:I,if (J).fire (owner i)=s then charge i*solo owner grades sites T A h t i z else 0:=by
  let f:=fun (a:Index owner grades T)(p:PagesOf n N)=>if (M a).mode=s then token h M t a p z else 0
  have sum:Summable (fun a:Index owner grades T=>∑p:PagesOf n N,f a p):=by
    apply summable_sum;intro p _
    apply (collects h M t stock σpos (fun i _=>(M i).mode=s) p z).congr
    intro a;by_cases ok:(M a).mode=s <;> simp [f,ok]
  have same:frame h M t (fun i _=>(M i).mode=s) z=(∑'a:Index owner grades T,∑p:PagesOf n N,f a p):=by
    unfold frame;apply tsum_congr;intro a;apply sum_congr rfl;intro p _
    by_cases ok:(M a).mode=s <;> simp [f,ok]
  rw [same,sum.tsum_sigma,tsum_fintype]
  apply Finset.sum_congr rfl;intro i _
  by_cases eq:(J).fire (owner i)=s
  · rw [if_pos eq]
    unfold solo frame
    rw [←tsum_mul_left]
    apply tsum_congr;intro y
    rw [mul_sum]
    apply Finset.sum_congr rfl;intro p _
    simp only [f,WilsonOriginalPointCompactRoster.support,eq,if_true]
    exact letter owner grades sites T A charge h t i y p z
  · rw [if_neg eq]
    have gone:(fun y:(T i).Roster=>∑p:PagesOf n N,f ⟨i,y⟩ p)=(fun _=>0):=by
      funext y;apply sum_eq_zero;intro p _;simp [f,WilsonOriginalPointCompactRoster.support,eq]
    rw [gone];simp

theorem filed {w:Fin 3→ℝ} {σ₀ C:ℝ} {d seats shelf:ℕ} (stock:Scene.Armada M w grades σ₀ C d seats shelf)
    (σpos:0<σ₀) (s:Hot (J)) (L:Layout G) (tape:Finset Age) (z:Joint G N):
    (TwoReset.copyColor h M grades (fun i=>(M i).paint t) L tape).mark s z.1 (RG.increment 1 z.2)=
      ∑i:I,if (J).fire (owner i)=s.val then charge i*solo owner grades sites T A h t i z else 0:=
  (WilsonOriginalOccupiedFieldLayout.filed h M t stock σpos L tape s z).symm.trans
    (collected owner grades sites T A charge h t stock σpos s.val z)

end YM.Integration.WilsonOriginalThreeCopiedWords
