import YM.Integration.WilsonVacuumPreResetDatedDeposit
import YM.Integration.FVA1Physical.TwoReset.VacPolicy

/-! The affine mass calculation along one funded quiet trajectory. Each deposited layout is reused at the next step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDatedCourse
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice

open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe

noncomputable abbrev coin (N j:ℕ):Pace.Coin:=
  Tested.term (pitch (levels R) (ratio R) N j-1)

theorem affine (simple:G.Simple){N j e:ℕ}(hj:j<N){Z Z':SeriesA G}{σ C σ' C':ℝ}
    (lo:Issued R N j e Z σ C)(hi:Issued R N (j+1) e Z' σ' C'):
    AffineMass R hj (bank Z') (bank Z) (coin R N j) e:=by
  have unit:constantCoeff (pitch (levels R) (ratio R) N j)=1:=Bank.angle_tilt (A:=levels R) simple (RunFormalChain.fromRun R).receipt hj
  refine ⟨?_,?_,WilsonVacuumPreResetDatedDeposit.call R simple hj lo hi⟩
  · simp only [coin,Tested.term,coeff_zero_eq_constantCoeff_apply,map_sub,unit,map_one,sub_self]
  · intro j _
    exact ⟨σ,WilsonVacuumPreResetTorusDeposit.fee C Z j,lo.positive,
      WilsonVacuumPreResetTorusDeposit.quoted Z lo.purchase.2 (fun a ha=>lt_of_lt_of_le (by decide :0<3) (lo.lower a ha)) j⟩

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃ W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ, ∃ Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→ ∃ σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
        Issued R N j e (Z j) σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      (∀j,m≤j→j≤N→ AllOrder.Floe.Legal (Step.tape (e+2)) (bank (Z j))) ∧
      ∀j,m≤j→∀h:j<N,AffineMass R h (bank (Z (j+1))) (bank (Z j)) (coin R N j) e:=by
  classical
  obtain ⟨W,dates⟩:=WilsonVacuumPreResetDatedDeposit.original R simple v rows paths e
  obtain ⟨m₀,work⟩:=eventually_atTop.1 dates
  refine ⟨W,eventually_atTop.2 ⟨m₀,?_⟩⟩
  intro m hm N
  have pick (j:ℕ): ∃Z:SeriesA G, ∀_hm:m≤j,∀_hN:j≤N, ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
      Issued R N j e Z σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j):=by
    by_cases active:m≤j ∧ j≤N
    · obtain ⟨σ,good,width,budget⟩:=work j (hm.trans active.1)
      obtain ⟨Z,bill⟩:=budget N active.2
      exact ⟨Z,fun _ _=>⟨σ,good,width,bill⟩⟩
    · exact ⟨[],fun lo hi=>(active ⟨lo,hi⟩).elim⟩
  choose Z paid using pick
  refine ⟨Z,paid,?_,?_⟩
  · intro j lo hi
    obtain ⟨σ,_,_,a⟩:=paid j lo hi
    exact WilsonVacuumPreResetTorusDeposit.legal (Z j) a.positive a.purchase a.lower _
  · intro j lo hi
    obtain ⟨σ,_,_,a⟩:=paid j lo hi.le
    obtain ⟨τ,_,_,b⟩:=paid (j+1) (lo.trans (Nat.le_succ _)) hi
    exact affine R simple hi a b

end YM.Integration.WilsonVacuumPreResetDatedCourse
