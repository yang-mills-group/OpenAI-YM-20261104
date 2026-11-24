import YM.Integration.WilsonIndependentConditionedPairFour

/-! A single numeric allowance for each admitted pair, determined before the individual pivot tests. It keeps both source incomes and their own relative inverse tickets. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairTrialCost
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentMatchedRosterMasks (Bits)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonIndependentConditionedPairFour (Assigned)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

def unitName {h:ℕ}(F:Labels.Frame G h):Alma F:=
  ⟨(0,⟨0,by simp⟩),by simpa only [rankS,Multiset.card_zero,Nat.add_zero] using F.bound 0⟩

theorem starts_unit {h:ℕ}(F:Labels.Frame G h):F.basis (sheet F (unitName F))=Labels.unit G h:=F.starts_unit

def roof (f:Bits 1→ℝ):ℝ:=max 0 (max (f (true,true)) (max (f (true,false)) (f (false,true))))

private theorem grow {H:Hol G}{Q:SealR G}{rail:Rails Q.h k u₀ e}{E W K U:Credit}
    (X:CutsP H Q.ans Q.path rail E W K U)(P Q':Era G ℝ)(host u:ℕ){A B:ℝ}
    (paid:Hearing X P Q' host u A)(bigger:A ≤ B):Hearing X P Q' host u B:=
  ⟨⟨paid.1.1.trans bigger,fun i hi r hr=>(paid.1.2 i hi r hr).more bigger⟩,
    fun i hi z=>(paid.2 i hi z).trans bigger⟩

theorem original {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{u b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(pick:(s:J)→ι s)
    (ζ:ℝ)(a B:J→ℝ)(t z:ℝ)(gain:ζ ≤ 1/4)(room:((∑s,(Q s).h:ℕ):ℝ)+ζ < b)(ht:0<t):
    let X:=fun s=>T.cuts s (pick s)
    let f:=charge Q own C C C C V X coins u b host m K ζ a B t z
    let η:=roof f
    0 ≤ η ∧ ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR),
      (∀s s',s≠s'→ClearDay (φ s) (φ s') t) → (∀s,radiusH (φ s) 1 y ≤ z) →
      (∀s,Amplitude (φ s) (B s)) →
      let Δ:=fun s:J=>seat (X s) (a s) (φ s) y o (X s).i
      let P:=fun (s:J)(j:Alma (Q s).F)=>film (X s) j 0 (φ s) y o (X s).i
      Hearing (X 0) (Δ 0) (Δ 1) host u η ∧
        (∀j,Hearing (X 1) (Δ 0) (P 1 j) host u η) ∧
        (∀j,Hearing (X 0) (P 0 j) (Δ 1) host u η):=by
  intro X f η
  refine ⟨le_max_left ..,?_⟩
  intro φ y o clearance sizes bounds Δ F
  obtain ⟨both,left,right⟩:=T.heard pick ζ a (fun s=>unitName (Q s).F) φ y t z o B
    gain room ht clearance sizes bounds
  have stable:f (true,true) ≤ η:=(le_max_left ..).trans (le_max_right ..)
  have leftFee:f (true,false) ≤ η:=(le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have rightFee:f (false,true) ≤ η:=(le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  exact ⟨grow (X 0) (Δ 0) (Δ 1) host u both stable,
    fun j=>grow (X 1) (Δ 0) (F 1 j) host u (left j) leftFee,
    fun j=>grow (X 0) (F 0 j) (Δ 1) host u (right j) rightFee⟩

end YM.Integration.WilsonIndependentConditionedPairTrialCost
