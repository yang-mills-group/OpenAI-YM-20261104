import YM.Integration.WilsonOriginalCensusCopiedColors
import YM.Integration.WilsonOriginalThreeCopiedCharts
import YM.Integration.WilsonGeneralArityCopyAccount

/-! Read every separately earned one-color row of the printed upper input on its original
auxiliary pages. Shared occupied modes keep the sum of all of their recorded binders. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCopySlate
open Function Finset Lattice Laurent Wilson RG Marker QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalMixedBlockRows WilsonOriginalPaidWalkCover WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonRegisteredPairUnaryWallet (disk)
open WilsonOriginalThreeCopiedCharts (name)
open WilsonOlderFreshGraphSlate (Copy)
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(B:I→Binder P (Stock.census V))(grades:V→ℕ)
  {q:ℕ}{σ:ℝ}(T:∀i,Copy G (∑v∈(B i).mode.val,grades v) q σ)
  (div:n.val∣N.val)(x:Wallet (room V))(π:Layout G)(tape:Finset Age)
local notation "own" i:max => (T (i)).rows (WilsonOlderFreshGraphPointWallet.point (B (i)).center) disk
local notation "M" => mounted B (fun i=>own i)
local notation "J" => Stock.census V
def color (i:I):=copyColor div (own i) (fun _=>∑v∈(B i).mode.val,grades v)
  (fun z=>((own i) z).paint (project (B i).mode x)) π tape

theorem filed {w:V→ℝ}{σ₀ C:ℝ}{order seats shelf:ℕ}
    (whole:Scene.Armada M w grades σ₀ C order seats shelf)(width:0<σ₀)(hs:0<σ)
    (s:Hot (J))(y:Joint G N):
    (copyColor div M grades (fun i=>(M i).paint x) π tape).mark s y.1 (RG.increment 1 y.2)=
    ∑i:I,if (B i).mode=s.val then
      (color B grades T div x π tape i).mark name y.1 (RG.increment 1 y.2) else 0:=by
  rw [WilsonOriginalCensusCopiedColors.original B (fun i=>own i) div x whole width s π tape y]
  apply sum_congr rfl
  intro i _
  split_ifs with present
  · let d:=∑v∈(B i).mode.val,grades v
    have stock:= (WilsonGeneralArityCopyAccount.original (T i) (B i).center hs.le
      (ord:=q) (seats:=1) (shelf:=d) le_rfl le_rfl le_rfl).1
    have select:(fun _:(T i).Roster=>fun _:PagesOf n N=>True)=
      (fun z=>fun _=>((own i) z).mode=name.val):=by
      funext z p
      exact propext (iff_true_intro (show ((own i) z).mode=name.val from rfl)).symm
    rw [select]
    exact WilsonOriginalOccupiedFieldLayout.filed div (own i) (project (B i).mode x) stock hs π tape name y
  · rfl

theorem received {p':Passport n V}{μ:Type}(high:μ→Row p' (J) G (Wallet (room V)))
    (placed:p'=P)(names:μ=((i:I)×(T i).Roster))(ink:HEq high M)
    {w:V→ℝ}{σ₀ C:ℝ}{order seats shelf:ℕ}
    (whole:Scene.Armada high w grades σ₀ C order seats shelf)(width:0<σ₀)(hs:0<σ)
    (s:Hot (J))(y:Joint G N):
    (copyColor div high grades (fun i=>(high i).paint x) π tape).mark s y.1 (RG.increment 1 y.2)=
    ∑i:I,if (B i).mode=s.val then
      (color B grades T div x π tape i).mark name y.1 (RG.increment 1 y.2) else 0:=by
  subst p' μ
  cases eq_of_heq ink
  exact filed B grades T div x π tape whole width hs s y

end YM.Integration.WilsonOriginalCensusCopySlate
end
