import YM.Integration.WilsonIndependentConditionedBankFour
import YM.Integration.WilsonIndependentConditionedBankMatrix

/-! Actual relative pair error on two previously assigned numerical public coordinates. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankFrame
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankFour (Enrolled)
open WilsonIndependentConditionedBankMatrix (sample protocol)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentConditionedBankPublicGram (residual)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedMixedCash (embed)
open WilsonOlderFreshSoftCoverScalar (clock)

theorem allowance (a b x y s u κ:ℝ)(hx:0≤x)(hy:0≤y)(hk:0≤κ):
    κ*((1+a*x)*(1+b*y)+s)+u≤(κ*((1+|a|)*(1+|b|)+|s|)+|u|)*((1+x)*(1+y)):=by
  have leg (a x:ℝ)(hn:0≤x):|1+a*x|≤(1+|a|)*(1+x):=calc
    _ ≤ |(1:ℝ)|+|a*x|:=abs_add_le .. 
    _ ≤ _:=by rw [abs_one,abs_mul,abs_of_nonneg hn];nlinarith only [hn,abs_nonneg a]
  have prod:(1+a*x)*(1+b*y)≤((1+|a|)*(1+|b|))*((1+x)*(1+y)):=calc
    _ ≤ |(1+a*x)*(1+b*y)|:=le_abs_self _
    _ = |1+a*x| *|1+b*y|:=abs_mul .. 
    _ ≤ ((1+|a|)*(1+x))*((1+|b|)*(1+y)):=mul_le_mul (leg a x hx) (leg b y hy) (abs_nonneg _) (by positivity)
    _ = _:=by ring
  have one:(1:ℝ)≤(1+x)*(1+y):=by nlinarith [mul_nonneg hx hy]
  have extra (s:ℝ):s≤|s| *((1+x)*(1+y)):=
    (le_abs_self s).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left one (abs_nonneg s))
  calc
    _ ≤ κ*(((1+|a|)*(1+|b|))*((1+x)*(1+y))+|s| *((1+x)*(1+y)))+|u| *((1+x)*(1+y)):=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add prod (extra s)) hk) (extra u)
    _ = _:=by ring

theorem original {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(older:host ≤ m)
    (L M:Credit)(income:Enrolled T L M)(a:(s:J)→ι s→ℝ)(q:ℕ)(order:q ≤ e)(g:ℝ)(small:|g| ≤ 1):
    let source:=fun s i=>publicDose (Q s) (T.cuts s i) (a s i)
    let v:=fun s i=>sample V (Q s) N m host q g (source s i)
    ∀(pick:(s:J)→ι s)(ζ:ℝ)(B:J→ℝ)(t z:ℝ),ζ ≤ 1/4 → ((∑s,(Q s).h:ℕ):ℝ)+ζ < b → 0<t →
    let X:=fun s=>T.cuts s (pick s); let α:=fun s=>a s (pick s)
    let f:=charge Q own C C C C V X coins u b host m K ζ α B t z
    let κ:=((q+1:ℕ):ℝ)*roof f
    let s:=2*|g|^(q+1)*(reserve (X 0) host q (dose (X 0) (α 0))+reserve (X 1) host q (dose (X 1) (α 1)))
    ∀(φ:(i:J)→Rarity (Q i).D)(y:ℝ)(o:CellR),
      (∀i j,i≠j→ClearDay (φ i) (φ j) t) → (∀i,radiusH (φ i) 1 y ≤ z) → (∀i,Amplitude (φ i) (B i)) → ∀w,
      let d:=fun i=>source i (pick i); let n:=fun i=>∑l,‖v i (pick i) l‖
      let row:=fun i=>input Q own C C C C X i (α i) (φ i) y o
      let G:=protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 w q g
      let high:=3*|g|^(q+1)*residual V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 w q (d 0) (d 1)
      let error:=κ*((1+|(X 0).vesselsC.cash L (X 0).m|)*(1+|(X 1).vesselsC.cash M (X 1).m|)+|s|)+|high|
      ‖view (X 0) host q g (row 0) (row 1) w-G (v 0 (pick 0)) (v 1 (pick 1))‖≤error*((1+n 0)*(1+n 1)):=by
  intro source v pick ζ B t z gain room ht X α f κ s φ y o apart sizes bounds w d n row G high error
  have bought:=income pick ζ α B t z gain room ht φ y o apart sizes bounds q order g small w
  have exactGram:=WilsonIndependentConditionedBankMatrix.original V (X 0) (X 1) m K N host older
    (T.levels 0 _) (T.reset 0 _) (T.home 0 _) (T.vacuum 0 _)
    (T.levels 1 _) (T.reset 1 _) (T.home 1 _) (T.vacuum 1 _) (α 0) (α 1) (φ 0) (φ 1) y o 0 w q g
  have measured (i:J):amount (X i) host q g (d i)=n i:=by
    change (∑l,‖cash q g (embed (clock (X i).ax (X i).tx (X i).N (X i).m host (d i l)))‖)=
      ∑l,‖cash q g (embed (clock V.draws V.paid N m host (d i l)))‖
    rw [T.levels,T.reset,T.vacuum,T.home]
  have hκ:0≤κ:=mul_nonneg (by positivity) (le_max_left ..)
  have hn (i:J):0≤n i:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have diff:‖view (X 0) host q g (row 0) (row 1) w-G (v 0 (pick 0)) (v 1 (pick 1))‖≤
      κ*((1+(X 0).vesselsC.cash L (X 0).m*n 0)*(1+(X 1).vesselsC.cash M (X 1).m*n 1)+s)+high:=by
    change ‖view (X 0) host q g (row 0) (row 1) w-
        response V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 w q g (d 0) (d 1)‖≤
      κ*((1+(X 0).vesselsC.cash L (X 0).m*amount (X 0) host q g (d 0))*
      (1+(X 1).vesselsC.cash M (X 1).m*amount (X 1) host q g (d 1))+s)+high at bought
    rw [exactGram,measured,measured] at bought
    exact bought
  exact diff.trans (allowance _ _ _ _ s high κ (hn 0) (hn 1) hκ)

end YM.Integration.WilsonIndependentConditionedBankFrame
