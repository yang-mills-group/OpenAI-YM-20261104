import YM.Integration.WilsonIndependentConditionedGramHomogeneity

/-! The three nonempty compensated faces on a two-source board. The same
maximum controls the unscaled annular return and the holder with its
explicit spacing power. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramShellLifetime
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedGramHomogeneity (paid)
open scoped BigOperators Topology Classical
local notation "J" => Fin 2
variable {G:Gauge}

theorem original (R:Run G)(Q:J→SealR G)(coins:Prices)(k e u b host m K:ℕ)
    (ζ η δ:ℝ)(a A B H:J→ℝ)(t z:ℝ)(pos:0<δ)(small:δ ≤ 1)(nonneg:0 ≤ ζ)(room:2*η ≤ ζ/4)
    (inlet:∀s,0 ≤ |a s| *A s)(source:∀s,|a s| *A s ≤ H s*δ^(-η)):
    let W:=wage (k:=k) (e:=e) R Q coins u b host m K ζ a A B t z
    let W₀:=wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z
    roof W ≤ δ^(-(ζ/4))*roof W₀*(1+H 0)*(1+H 1) ∧
      δ^ζ*roof W ≤ δ^(3*ζ/4)*roof W₀*(1+H 0)*(1+H 1):=by
  intro W W₀
  let c:=δ^(-(ζ/8))
  have cpos:1 ≤ c:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos pos small (by linarith only [nonneg])
  have cheap:δ^(-η) ≤ c:=Real.rpow_le_rpow_of_exponent_ge pos small (by linarith only [room])
  have coef (s:J):0 ≤ H s:=by
    by_contra! neg
    exact (not_lt_of_ge ((inlet s).trans (source s))) (mul_neg_of_neg_of_pos neg (Real.rpow_pos_of_pos pos _))
  have Wpos:0 ≤ roof W₀:=le_max_left ..
  have c2:c*c=δ^(-(ζ/4)):=by
    dsimp only [c]
    rw [←Real.rpow_add pos]
    congr 1
    ring
  have mask (s:Bits 1)(under:W₀ s ≤ roof W₀):
      W s ≤ δ^(-(ζ/4))*roof W₀*(1+H 0)*(1+H 1):=by
    let B₁:=fun j:J=>if choose 1 s j then |a j| *A j else 1
    have pay (j:J):0 ≤ B₁ j ∧ B₁ j ≤ c*(1+H j):=by
      cases hit:choose 1 s j
      · simp only [B₁,hit,Bool.false_eq_true,if_false]
        exact ⟨zero_le_one,one_le_mul_of_one_le_of_one_le cpos (by linarith only [coef j])⟩
      · simp only [B₁,hit,if_true]
        refine ⟨inlet j,(source j).trans ?_⟩
        calc
          _ ≤ H j*c:=mul_le_mul_of_nonneg_left cheap (coef j)
          _ ≤ c*(1+H j):=by linarith only [cpos]
    have size:paid s a A=B₁ 0*B₁ 1:=Fin.prod_univ_two B₁
    have fact:=WilsonIndependentConditionedGramHomogeneity.original R Q coins k e u b host m K ζ a A B t z s
    change W s=W₀ s*paid s a A at fact
    rw [fact,size]
    calc
      _ ≤ roof W₀*(c*(1+H 0)*(c*(1+H 1))):=
        mul_le_mul under (mul_le_mul (pay 0).2 (pay 1).2 (pay 1).1
          (mul_nonneg (zero_le_one.trans cpos) (by linarith only [coef 0])))
          (mul_nonneg (pay 0).1 (pay 1).1) Wpos
      _=δ^(-(ζ/4))*roof W₀*(1+H 0)*(1+H 1):=by rw [←c2];ring
  have cash:roof W ≤ δ^(-(ζ/4))*roof W₀*(1+H 0)*(1+H 1):=by
    have pp:0 ≤ δ^(-(ζ/4)):=Real.rpow_nonneg pos.le _
    unfold WilsonIndependentConditionedPairTrialCost.roof
    exact max_le (mul_nonneg (mul_nonneg (mul_nonneg pp Wpos) (by linarith only [coef 0])) (by linarith only [coef 1]))
      (max_le (mask (true,true) ((le_max_left ..).trans (le_max_right ..)))
       (max_le (mask (true,false) ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))))
         (mask (false,true) ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))))))
  refine ⟨cash,(mul_le_mul_of_nonneg_left cash (Real.rpow_nonneg pos.le _)).trans_eq ?_⟩
  have refund:δ^ζ*δ^(-(ζ/4))=δ^(3*ζ/4):=by rw [←Real.rpow_add pos];congr 1;ring
  rw [←refund]
  ring

end YM.Integration.WilsonIndependentConditionedGramShellLifetime
