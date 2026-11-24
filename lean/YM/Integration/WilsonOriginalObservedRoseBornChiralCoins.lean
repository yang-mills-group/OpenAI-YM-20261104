import YM.Integration.WilsonOriginalObservedRoseBornChiralPeer
import YM.Integration.WilsonIndependentMatchedFreshPriceBook

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralCoins
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix cancel)
open WilsonPositionProgramTrialPublicJointSourceStable (seen)
open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical Topology

open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
variable {G:Gauge}{n k u e h D₀:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

open WilsonIndependentMatchedFreshInverseIncome (slope measured age)
open WilsonIndependentMatchedProxyIncome (cost)
open WilsonOriginalObservedRoseBornChiralPeer (input)
open PowerSeries WilsonCoeffUV.Bank.Mosaic

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:WilsonMaxwellThermometerSurveyIncome.prices W R.kit)(big:h<D₀)(rails:Rails h k u e)
    (cap:capP (deck (G:=G) d D fit) ≤ k):
    let J:=port R W d D fit false
    ∃A:Fin (n+1)→Bool→Credit,∃B:Fin (n+1)→Credit,∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K →
    ∀i (b:(J i).Rider) side,
    let price := (Fintype.card (Alma (J i).F):ℝ)*(B i).buy (zz L m)*cost e b
    ∀t ≤ e,∀a,‖coeff t (PermuteLens L O (J i) K m b a)‖ ≤ price ∧
      ‖coeff t (input R W d D fit side i m K b a)‖ ≤ (A i side).buy (age L (zz L) m K)*price:=by
  intro J
  choose A purchase using fun i side=>slope (hol G) (port R W d D fit side i) e
  choose B gate using fun i=>belt (H:=hol G) (C:=CC) (T:=(J i).ans) (p:=(J i).path) (e:=e) (E:=CC) (W:=CC)
  refine ⟨A,B,?_⟩
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W d D fit simple v funded pub big rails cap] with j sale
  obtain ⟨_,chair,levels,clock,calendar,floor,_,_,_,school⟩:=sale
  intro m K start before i b side price t ht a
  let f:AheadT (hol G) chair.L.V CC CC (J i) CC:=((school (fun _=>false)).1 i).some
  let g:AheadT (hol G) chair.L.V CC CC (port R W d D fit side i) CC:=by
    cases side
    · exact ((school (fun _=>false)).1 i).some
    · exact ((school (fun _=>true)).1 i).some
  have entered:f.p.f.arch.V.anchor ≤ m:=by rw [f.p.tap,floor]; exact start
  have both:g.p.f.arch.V.anchor ≤ m:=by rw [g.p.tap,floor]; exact start
  have hot:1 ≤ zz L m:=by simpa only [f.p.depths,calendar] using f.p.f.arch.V.depth m entered
  have pos:0 ≤ (B i).buy (zz L m):=zero_le_one.trans ((B i).purchase hot)
  have inverse (x y:Alma (J i).F):‖(Wray L O (J i).ans (J i).path K m)⁻¹ x y‖ ≤ (B i).buy (zz L m):=by
    have bound:=(gate i f.p.f.arch f.stamps m m K K entered le_rfl before before x y).main
    simpa only [Realm.cash,f.p.lands,f.p.modes,f.p.depths,levels,clock,calendar] using bound
  have common (q:ℕ)(hq:q≤e)(a:Alma (J i).F):‖coeff q (PermuteLens L O (J i) K m b a)‖ ≤ price:=
    measured L O (J i) K m b q _ _ pos (WilsonIndependentMatchedProxyIncome.charged b q hq) inverse a
  have paid:=purchase i side g.p.f m K both before (PermuteLens L O (J i) K m b) price
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pos) (WilsonIndependentMatchedProxyIncome.nn b)) common t ht a
  have top:input R W d D fit side i m K b=
      steep L O (port R W d D fit side i).ans (fit i) K m (K-m) (PermuteLens L O (J i) K m b):=by
    cases side <;> rfl
  refine ⟨common t ht a,?_⟩
  simpa only [top,g.p.lands,g.p.modes,g.p.depths,levels,clock,calendar] using paid

end YM.Integration.WilsonOriginalObservedRoseBornChiralCoins
