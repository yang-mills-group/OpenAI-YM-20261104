import YM.Integration.WilsonNeutralTwoPrintPathPortfolio
import YM.Integration.WilsonOriginalPrimerCourseRead

/-! The deposited census' actual budget supplies its full angular read by the original separately paid lower compact prints. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathMounted
set_option quotPrecheck false
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical FVA1Physical.TwoReset QuadraticLocal.Affinity Comparison.RG02
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOlderFreshGraphSlate
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I]{G:Gauge}{n:Side}
  {P:Passport n V}(B:I→Binder P (Stock.census V))(grades:V→ℕ){q:ℕ}{σ:ℝ}
local notation "level" i:max => ∑v∈(B i).mode.val,grades v
variable (T:∀i:I,Copy G (∑v∈(B i).mode.val,grades v) q σ)
local notation "site" i:max => WilsonOlderFreshGraphPointWallet.point (B i).center
local notation "X" => fun i=>(T i).rows (site i) disk
local notation "M" => mounted B (X)

theorem original {w:V→ℝ}{σ₀ expense:ℝ}{order seats shelf:ℕ}
    (bought:Scene.Armada (M) w grades σ₀ expense order seats shelf)(staffed:0<σ₀)(width:0<σ)
    (x:Wallet (room V))(layout:Layout G)(tape:Finset Age)(s:Hot (Stock.census V))(e:ℕ)(Y:Link G n):
    (peek dvd_rfl (M) grades layout tape x e Y).part s.val=
      ∑i,if s.val=(B i).mode then
        (peek dvd_rfl ((T i).rows (site i) disk) (fun _=>level i) layout tape
          (project (B i).mode x) e Y).part (site i).mode else 0:=by
  have allRows:=Air.license (M) (fun z=>((M) z).paint x) grades w bought staffed (fun z=>bought.honor z x)
  have cap:∀t:Wallet disk,‖value disk t‖≤1:=fun t=>(t ()).property
  have paid (i:I):Air.Staff ((T i).rows (site i) disk)
      (fun z=>((T i).rows (site i) disk z).paint (project (B i).mode x)) (fun _=>level i) σ (q+(level i)+1):=
    WilsonOriginalPrimerCourseRead.salary (site i) (T i).roll (T i).fare σ (T i).paid (T i).legal
      (T i).positive disk cap (project (B i).mode x) width
  exact WilsonNeutralTwoPrintPathPortfolio.original B (X) (fun _ _=>rfl) x grades (fun i _=>level i)
    allRows paid layout tape s e Y

theorem received {p':Passport n V}{μ:Type}(low:μ→Row p' (Stock.census V) G (Wallet (room V)))
    (placed:p'=P)(names:μ=((i:I)×(T i).Roster))(ink:HEq low (M))
    {w:V→ℝ}{σ₀ expense:ℝ}{order seats shelf:ℕ}
    (bought:Scene.Armada low w grades σ₀ expense order seats shelf)(staffed:0<σ₀)(width:0<σ)
    (x:Wallet (room V))(layout:Layout G)(tape:Finset Age)(s:Hot (Stock.census V))(e:ℕ)(Y:Link G n):
    (peek dvd_rfl low grades layout tape x e Y).part s.val=
      ∑i,if s.val=(B i).mode then
        (peek dvd_rfl ((T i).rows (site i) disk) (fun _=>level i) layout tape
          (project (B i).mode x) e Y).part (site i).mode else 0:=by
  subst p' μ
  cases eq_of_heq ink
  exact original B grades T bought staffed width x layout tape s e Y

end YM.Integration.WilsonNeutralTwoPrintPathMounted
end
