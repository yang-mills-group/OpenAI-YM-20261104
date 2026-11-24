import YM.Integration.WilsonSeparatedPrefixMovingFiledFiscal
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceSides
import YM.Integration.WilsonSeparatedPrefixMovingFiledSeats
import YM.Integration.WilsonIndependentMovingRosterAllFineClock
import YM.Integration.WilsonThermometerAncestralCalendar

/-! The engineering power of the actual measured station salary on its
original optical window is fixed by its field height before the finite
thermal order is selected. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFrozenAge
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations WilsonLimitConstruction XSpace
open WilsonPositionProgramTrialStationHome (chargeAt elapsed)
open WilsonCoeffUV.Bank.Ticket (zz)
open private salary from YM.Integration.WilsonIndependentMovingRosterAllFineClock
open scoped BigOperators Classical
variable {G:Gauge}

open WilsonPositionProgramTrialPublicJointSourceVote (port)
open WilsonPositionProgramTrialPublicJointSourceSides (Courts)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonPositionProgramTrialStationHome (dates)

theorem same {n k u e:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
    (w:∀i,Rails (d i) k u e)(V:Realm G (e+1) Credit.leanC)(X Y:Courts R W d D fit w)
    (kind:Fin (n+1)→Bool)(field:∀i,Verse (R.family.labels.level (d i)))(α:∀i,Alma (R.family.labels.level (d i))→ℝ)
    (Z B:Fin (n+1)→Credit)(m K N:ℕ)(level:V.draws=R.family.path.levels)
    (file:Filed R W d D fit kind w field α Z B m K N X)(born:stamp V Y m K K)
    (law:∀i,(Y i).L=(X i).L)(i:Fin (n+1)):
    (Y i).Age=WilsonPositionProgramTrialStationHome.age R.family.path.levels m K:=by
  have clock:(Y i).vesselsC.y=zz R.family.path.levels:=by
    change (Y i).L.L.V.y=_
    rw [law]
    exact (file i).1.2.2.2.2.2.1
  exact (dates (Y i) _ m K ((born i).1.trans level) clock (born i).2.2.1 (born i).2.2.2.1).2

theorem credits (P:Run G)(simple:G.Simple)(C:Credit)(A η:ℝ)(ap:0 ≤ A)(gain:0<η):
    ∀ᶠ m:ℕ in atTop,∀K N per:ℕ,m ≤ K → K ≤ N →
    let L:=P.family.path.levels
    let g:=Pert.Asymptotics.regulatorRun P.family N per m
    L.S.a m/L.S.a K ≤ g^(-A) → ∀t:ℝ,1 ≤ t → t ≤ WilsonPositionProgramTrialStationHome.age L m K →
      |C.buy t| ≤ g^(-η):=by
  obtain ⟨x₀,invest⟩:=eventually_atTop.1 (salary C (8+2*A) η gain)
  let v:=max 1 x₀
  filter_upwards [(RG01.Physical.hats simple P.family.path.levels).eventually_ge_atTop (max 3 (9*Real.exp (2*v)))]
    with m late K N per low top L g opt t one cost
  have hp:=WilsonSeparatedPrefixMovingFiledFiscal.heat P m N per (low.trans top)
  have gp:0<g:=hp.1
  have cold:3 ≤ L.clock.hatBeta m:=(le_max_left _ _).trans late
  have hot:9*Real.exp (2*v) ≤ (3*g⁻¹)^2:=((le_max_right _ _).trans late).trans hp.2
  have high:v ≤ -Real.log g:=by
    have ineq:Real.exp (2*v) ≤ (g⁻¹)^2:=by nlinarith only [hot]
    have logged:=Real.log_le_log (Real.exp_pos _) ineq
    rw [Real.log_exp,Real.log_pow,Real.log_inv] at logged;norm_num at logged;linarith only [logged]
  have sale:=WilsonSeparatedPrefixMovingFiledFiscal.window P m K N per low top A ap cold ((le_max_left ..).trans high) opt
  rw [abs_of_nonneg (zero_le_one.trans (Credit.purchase C one)),Real.rpow_def_of_pos gp]
  have wage:=invest (-Real.log g) ((le_max_right ..).trans high) t (zero_le_one.trans one) (cost.trans sale.2.2.1)
  exact wage.trans_eq (by congr 1;ring)

end YM.Integration.WilsonSeparatedPrefixMovingFrozenAge
