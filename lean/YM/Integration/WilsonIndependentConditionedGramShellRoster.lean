import YM.Integration.WilsonIndependentConditionedGramShellLifetime

/-! Restore each actual assigned source exactly once at its occupied
slots. Source nonnegativity is provided by the genuine finite cut. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramShellRoster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedGramHomogeneity (paid)
open scoped BigOperators Topology Classical
local notation "J" => Fin 2
local notation "C" => Credit.leanC
variable {G:Gauge}{e k u u₀:ℕ}

theorem appointed {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}
    {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(openDate:j ≤ host)(older:host ≤ m)
    (cut:m ≤ K)(ageV:V.y=zz R.family.path.levels)(pick:(s:J)→ι s)
    (ζ η:ℝ)(a B H:J→ℝ)(t z:ℝ)(positive:0 ≤ ζ)(room:2*η ≤ ζ/4)
    (source:∀s,|a s| *A s (pick s) ≤ H s*(paceT R.family.path.levels.S m K)^(-η)):
    let X:=fun s=>T.cuts s (pick s)
    let δ:=paceT R.family.path.levels.S m K
    let f:=charge Q own C C C C V X coins u b host m K ζ a B t z
    let A₀:=fun s=>A s (pick s)
    let W:=wage (k:=k) (e:=e) R Q coins u b host m K ζ a A₀ B t z
    let W₀:=wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z
    (∀mask,f mask=W₀ mask*paid mask a A₀*δ^ζ) ∧
      roof W ≤ δ^(-(ζ/4))*roof W₀*(1+H 0)*(1+H 1) ∧
      roof f ≤ δ^(3*ζ/4)*roof W₀*(1+H 0)*(1+H 1):=by
  intro X δ f A₀ W W₀
  have sourceNN (s:J):0 ≤ |a s| *A₀ s:=
    mul_nonneg (abs_nonneg _) (by
      change 0 ≤ A s (pick s)
      rw [←T.price s (pick s)]
      exact (X s).hf)
  have exactFee:=WilsonIndependentConditionedBankShellPrice.original T openDate older ageV pick ζ a B t z
  obtain ⟨high,low⟩:=WilsonIndependentConditionedGramShellLifetime.original R Q coins k e u b host m K
    ζ η δ a A₀ B H t z (pace_pos ..) (pace_le _ cut) positive room sourceNN source
  refine ⟨fun mask=>?_,high,?_⟩
  · rw [show f mask=W mask*δ^ζ from exactFee.1 mask,
      show W mask=W₀ mask*paid mask a A₀ from WilsonIndependentConditionedGramHomogeneity.original ..]
  · rw [show roof f=roof W*δ^ζ from exactFee.2,mul_comm (roof W)]
    exact low

end YM.Integration.WilsonIndependentConditionedGramShellRoster
