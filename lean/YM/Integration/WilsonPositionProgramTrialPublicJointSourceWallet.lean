import YM.Integration.WilsonPositionProgramTrialPublicJointSourceVote
import YM.Integration.WilsonIndependentMatchedFreshPriceBook

/-! The survey re-entry is charged directly to the measured registered vector. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceWallet
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialPublicJointSourceExchange (change carried)
open WilsonIndependentMatchedFreshWhole (projected)
open scoped BigOperators Classical Topology

variable {G:Gauge}{n h H k u e:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonIndependentMatchedFreshInverseIncome (slope measured age)

def row (side:Bool)(m K:ℕ)(i:Fin (n+1))(b:Verse (R.family.labels.level (d i))):Verse (R.family.labels.level (d i)):=
  let S:=port R W d D fit side i
  steep L O S.ans S.path K m (K-m) (PermuteLens L O (port R W d D fit false i) K m b)

theorem registered (m K:ℕ)(i:Fin (n+1))(b:Verse (R.family.labels.level (d i))):
    row R W d D fit false m K i b=received L O (port R W d D fit false i) m K K b:=rfl

theorem surveyed (m K:ℕ)(i:Fin (n+1))(b:Verse (R.family.labels.level (d i))):
    row R W d D fit true m K i b=refill R W d D fit m K i b:=rfl

def tickets {d:ℕ}{F:Labels.Frame G d}(e:ℕ)(A:Alma F→ℝ):ℝ:=
  ∑a,∑t∈Finset.range (e+1),∑_w∈Finset.HasAntidiagonal.antidiagonal t,A a

theorem tuition {d:ℕ}{F:Labels.Frame G d}(e:ℕ)(c:Verse F)(A:Alma F→ℝ)(a0:∀i,0 ≤ A i)
    (M:ℝ)(earned:∀t ≤ e,∀i,‖PowerSeries.coeff t (c i)‖ ≤ M):
    WilsonIndependentMatchedFiledIncome.charge e c A ≤ M*tickets e A:=by
  unfold WilsonIndependentMatchedFiledIncome.charge WilsonIndependentMatchedFiledIncome.allot tickets
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro w hw
  have time:=Finset.HasAntidiagonal.mem_antidiagonal.mp hw
  have steps:=Finset.mem_range.mp hj
  exact mul_le_mul_of_nonneg_right (earned w.1 (by omega) i) (a0 i)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(big:h<H)(rails:Rails h k u e)(cap:capP (deck (G:=G) d D fit) ≤ k):
    ∃A:Bool→Fin (n+1)→Credit,∃B:Fin (n+1)→Credit,∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K →
      ∀side i (b:Verse (R.family.labels.level (d i)))(M:ℝ),0 ≤ M →
      (∀t ≤ e,∀a,‖PowerSeries.coeff t (b a)‖ ≤ M) → ∀t ≤ e,∀a,
      ‖PowerSeries.coeff t (row R W d D fit side m K i b a)‖ ≤
        (A side i).buy (age L (zz L) m K)*((Fintype.card (Alma (R.family.labels.level (d i))):ℝ)*(B i).buy (zz L m)*M):=by
  let J:=port R W d D fit false
  let S:=port R W d D fit
  choose A paid using fun side i=>slope (hol G) (S side i) e
  choose B bound using fun i=>belt (H:=hol G) (C:=CC) (T:=(J i).ans) (p:=(J i).path) (e:=e) (E:=CC) (W:=CC)
  refine ⟨A,B,?_⟩
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W d D fit simple v funded pub big rails cap] with j course
  obtain ⟨_,chair,levels,cash,calendar,base,_,_,_,seats⟩:=course
  intro m K late before side i b M nn input t depth a
  let f:AheadT (hol G) chair.L.V CC CC (J i) CC:=((seats (fun _=>false)).1 i).some
  let g:AheadT (hol G) chair.L.V CC CC (S side i) CC:=((seats (fun _=>side)).1 i).some
  have start:f.p.f.arch.V.anchor ≤ m:=by rw [f.p.tap,base];exact late
  have attend:g.p.f.arch.V.anchor ≤ m:=by rw [g.p.tap,base];exact late
  have hclock:1 ≤ zz L m:=by simpa only [f.p.depths,calendar] using f.p.f.arch.V.depth m start
  have pos:0 ≤ (B i).buy (zz L m):=zero_le_one.trans (Credit.purchase _ hclock)
  have wray (a b:Alma (J i).F):‖(Wray L O (J i).ans (J i).path K m)⁻¹ a b‖ ≤ (B i).buy (zz L m):=by
    have s:=(bound i f.p.f.arch f.stamps m m K K start le_rfl before before a b).main
    simpa only [Realm.cash,f.p.lands,f.p.modes,f.p.depths,levels,cash,calendar] using s
  let U:=(Fintype.card (Alma (J i).F):ℝ)*(B i).buy (zz L m)*M
  have nu:0 ≤ U:=mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pos) nn
  have allocated (r:ℕ)(hr:r ≤ e)(a:Alma (J i).F):
      ‖PowerSeries.coeff r (PermuteLens L O (J i) K m b a)‖ ≤ U:=
    measured L O (J i) K m b r M _ pos (input r hr) wray a
  have pr:=paid side i g.p.f m K attend before (PermuteLens L O (J i) K m b) U nu allocated t depth a
  simpa only [row,g.p.lands,g.p.modes,g.p.depths,levels,cash,calendar] using pr

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceWallet
