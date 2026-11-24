import YM.Integration.WilsonNeutralTwoPrintPathDatedReprint
import YM.Integration.WilsonOriginalDepositedCensus

/-! The complete physical mixed census reads each separately deposited lower compact on exactly its occupied subset. Each incoming amplitude is projected by the original multiparent wallet, before the angular sum. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPortfolio
set_option quotPrecheck false
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn
open scoped Topology BigOperators Classical
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet
open FVA1Physical FVA1Physical.TwoReset QuadraticLocal.Affinity Comparison.RG02
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I]{G:Gauge}{n:Side}{O:I→Type}
  {P:Passport n V}(B:I→Binder P (Stock.census V))
  (X:(i:I)→O i→Row (Passport.point (fun _:Unit=>(B i).center)) (Stock.census Unit) G (Wallet disk))
  (rooted:∀i z,(X i z).binder=WilsonOlderFreshGraphPointWallet.point (B i).center)
  (x:Wallet (room V))(grades:V→ℕ)(localGrades:I→Unit→ℕ)
local notation "M" => mounted B X
local notation "site" i:max => WilsonOlderFreshGraphPointWallet.point (B i).center
local notation "weight" i:max => project (B i).mode x

omit [Fintype I] in
include rooted in
theorem atom (i:I)(z:O i)(e:ℕ)(Y:Link G n):
    ((M) ⟨i,z⟩).markReceipt e Y=(X i z).markReceipt e Y:=by
  have center:(X i z).center=(B i).center:=by
    change (X i z).binder.center=_
    rw [rooted]
    rfl
  unfold Row.markReceipt
  rw [center]
  rfl

include rooted in
theorem original {σ:ℝ}{q:ℕ}(salary:Air.Staff (M) (fun z=>((M) z).paint x) grades σ q)
    {w:I→ℝ}{stamps:I→ℕ}
    (income:∀i,Air.Staff (X i) (fun z=>(X i z).paint (weight i)) (localGrades i) (w i) (stamps i))
    (layout:Layout G)(tape:Finset Age)(s:Hot (Stock.census V))(e:ℕ)(Y:Link G n):
    (peek dvd_rfl (M) grades layout tape x e Y).part s.val=
      ∑i,if s.val=(B i).mode then
        (peek dvd_rfl (X i) (localGrades i) layout tape (weight i) e Y).part (site i).mode else 0:=by
  rw [WilsonThermometerPositionFilmSelf.pupil]
  have together:=Air.basis (M) (fun z=>((M) z).paint x) grades salary layout tape Y s e
  rw [←together.tsum_eq,together.summable.tsum_sigma,tsum_fintype]
  apply sum_congr rfl
  intro i _
  let deposited:Hot (Stock.census Unit):=⟨(site i).mode,⟨(site i).front,(site i).east⟩⟩
  have localSum:=Air.basis (X i) (fun z=>(X i z).paint (weight i)) (localGrades i) (income i)
    layout tape Y deposited e
  have one (z:O i):(X i z).mode=(site i).mode:=by
    change (X i z).binder.mode=_
    rw [rooted]
  by_cases hit:s.val=(B i).mode
  · rw [if_pos hit,WilsonThermometerPositionFilmSelf.pupil,←localSum.tsum_eq]
    apply tsum_congr
    intro z
    simp only [Poly.part_send,one]
    change (if s.val=(B i).mode then _ else 0)=(if (site i).mode=(site i).mode then _ else 0)
    rw [if_pos hit,if_pos rfl,atom B X rooted]
    rfl
  · rw [if_neg hit]
    calc
      _=∑' _:O i,(0:ℂ):=by
        apply tsum_congr
        intro z
        rw [Poly.part_send]
        exact if_neg hit
      _=0:=by simp

end YM.Integration.WilsonNeutralTwoPrintPathPortfolio
end
