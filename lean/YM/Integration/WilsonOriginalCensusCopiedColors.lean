import YM.Integration.WilsonOriginalThreeCopiedWords
import YM.Integration.WilsonOriginalMixedBlockRows

/-! The actual colored high input of a deposited census. On each covering page, the whole
filed mode is precisely the sum of the one-color terms on the binders carrying that mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCopiedColors
open Function Finset Lattice Laurent Wilson RG Marker QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalMixedBlockRows WilsonOriginalPaidWalkCover WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonRegisteredPairUnaryWallet (disk)
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {O:I→Type} {P:Passport n V} (B:I→Binder P (Stock.census V))
  (X:∀i,O i→Row (Passport.point (fun _:Unit=>(B i).center)) (Stock.census Unit) G (Wallet disk))
  (div:n.val∣N.val)(t:Wallet (room V))
local notation "M" => mounted B X
local notation "J" => Stock.census V

omit [Fintype I] in
theorem word (i:I)(z:O i)(p:PagesOf n N)(y:Joint G N):
    token div M t ⟨i,z⟩ p y=token div (X i) (project (B i).mode t) z p y:=by
  unfold token
  rw [centered,centered]
  rfl

theorem original {w:V→ℝ}{grade:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grade σ C order seats shelf)(hs:0<σ)
    (s:Hot (J))(L:Layout G)(tape:Finset Age)(y:Joint G N):
    (copyColor div M grade (fun i=>(M i).paint t) L tape).mark s y.1 (RG.increment 1 y.2)=
    ∑i:I,if (B i).mode=s.val then frame div (X i) (project (B i).mode t) (fun _ _=>True) y else 0:=by
  rw [←WilsonOriginalOccupiedFieldLayout.filed div M t stock hs L tape s y]
  let f:=fun (a:(i:I)×O i)(p:PagesOf n N)=>if (M a).mode=s.val then token div M t a p y else 0
  have summable:Summable (fun a:(i:I)×O i=>∑p:PagesOf n N,f a p):=by
    apply summable_sum;intro p _
    apply (collects div M t stock hs (fun a _=>(M a).mode=s.val) p y).congr
    intro a
    by_cases ok:(M a).mode=s.val <;> simp [f,ok]
  have gathered:frame div M t (fun a _=>(M a).mode=s.val) y=(∑'a:(i:I)×O i,∑p:PagesOf n N,f a p):=by
    unfold frame;apply tsum_congr;intro a;apply sum_congr rfl;intro p _
    by_cases ok:(M a).mode=s.val <;> simp [f,ok]
  rw [gathered,summable.tsum_sigma,tsum_fintype]
  apply Finset.sum_congr rfl;intro i _
  by_cases present:(B i).mode=s.val
  · rw [if_pos present]
    unfold frame;apply tsum_congr;intro z
    apply Finset.sum_congr rfl;intro p _
    have inc:(M ⟨i,z⟩).mode=(B i).mode:=rfl
    simp only [f,inc,present,if_true]
    simpa only [present] using word B X div t i z p y
  · rw [if_neg present]
    have gone:(fun z:O i=>∑p:PagesOf n N,f ⟨i,z⟩ p)=(fun _=>0):=by
      funext z;apply sum_eq_zero;intro p _
      have inc:(M ⟨i,z⟩).mode=(B i).mode:=rfl
      simp [f,inc,present]
    rw [gone];simp

end YM.Integration.WilsonOriginalCensusCopiedColors
end
