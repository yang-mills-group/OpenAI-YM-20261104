import YM.Integration.WilsonPositionProgramClockPrefix
import YM.Integration.WilsonPositionProgramReversedQuiet
import YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
import YM.Integration.WilsonSubmittedCalendar

/-! Rates of the actual filed inverse clock, uniformly before the physical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramMeasuredClockTariff
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDepositedGeometric (source)
open QuadraticLocal.Earn AllOrder.Floe
open WilsonFiledPeriodSeam WilsonCoeffUV.Bank.Realm ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse
open scoped Classical BigOperators
open WilsonVacuumPreResetDatedCourse (coin)
open FVA1Physical.TwoReset (massJets)
open AllOrder.Floe
open FVA1Physical.TwoReset (Prescription AffineMass)
open AllOrder.Floe.Step.PlanV
open PhysicalNext PhysicalNext.Repeat Legato WilsonLimitConstruction Next.Foundations
open WilsonSubmittedPeriodSeam (price weight Bill)
open QuadraticLocal.Rebirth QuadraticLocal.Faith Comparison.RG02.Adjacent
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Winding RegulatorIR
open Comparison.RG02.Moving Comparison.RG02.Moving.Path
open WilsonVacuumPreResetDatedCourse (coin)
open WilsonVacuumPreResetFiniteHeatStep FundedMarkedCoverRows
open PertExtension.Series PertExtension.Series.Tested PositionX.Jet
variable {G:Gauge}

theorem measured (R:Run G)(simple:G.Simple){N m e:ℕ}{Z:ℕ → SeriesA G}{π:ℕ → Layout G}{Γ:ℕ → Pace.Coin}
    (aligned:Agrees R N m e Z π Γ){j:ℕ}(low:m ≤ j)(live:j < N)
    (origin:Γ j 0=0){k:ℕ}(room:k ≤ e+2)(grade rank:ℕ):
    ‖motion (Adjacent.money ((QuadraticLocal.Rebirth.caliber (Γ j) origin).back (e+2)) 0 grade rank) k‖ ≤ 
      rimJ (ratioHigh (levels R) (ratio R) N j) k rank:=by
  have unit:constantCoeff (pitch (levels R) (ratio R) N j)=1:=Bank.angle_tilt (A:=levels R) simple (RunFormalChain.fromRun R).receipt live
  apply WilsonPositionProgramClockPrefix.original _ _ _ _ _ room (pitch (levels R) (ratio R) N j) unit
  intro d hd
  change Γ j d+just 1 d=_
  rw [aligned.rates j low live d (hd.trans room)]
  simp only [coin,Tested.term,map_sub]
  have h:just 1 d=PowerSeries.coeff d (1:PowerSeries ℝ):=by
    by_cases hz:d=0 <;> simp [just,hz,PowerSeries.coeff_one]
  rw [h,sub_add_cancel]

theorem calendar (G:Gauge):∃v:ℕ → Gear G → ℝ,∃D:ℕ → ℕ,∀(R:Run G),G.Simple → 
    FundedMarkedCoverRows.prices v R.kit → ∀s:ℕ,∀ᶠm:ℕ in atTop,
    ∀ N, m < N → ∀ a:ℕ, a ≤ s → ∀ b:ℕ, b ≤ s  → rimJ (ratioHigh (levels R) (ratio R) N m) a b ≤ 
      (max 1 |zz R.family.path.levels m|)^(D s):=by
  classical
  choose f d sale using fun (s:ℕ)(a b:Fin (s+1))=>
    WilsonVacuumPreResetFiniteHeatCourse.reversion G s a.val b.val (Nat.le_of_lt_succ a.isLt)
  let v(t:ℕ)(I:Gear G):ℝ:=∑s∈range (t+1),∑a:Fin (s+1),∑b:Fin (s+1),|f s a b I|
  let D(s:ℕ):ℕ:=∑a:Fin (s+1),∑b:Fin (s+1),d s a b
  refine ⟨v,D,?_⟩
  intro R simple paid s
  let L:=R.family.path.levels
  have grows:Tendsto (fun j:ℕ=>L.clock.J (j+1)) atTop atTop:=L.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) s 0 0,grows.eventually_ge_atTop s] with m realm active
  obtain ⟨Q,draws,coupling,clock,anchor,_,_,_,budget⟩:=realm
  have hm:Q.anchor ≤ m:=anchor.le
  obtain ⟨_,_,cash⟩:=budget m le_rfl hm
  intro N live a ha b hb
  let i:Fin (s+1):=⟨a,by omega⟩
  let l:Fin (s+1):=⟨b,by omega⟩
  let I:Gear G:=(Q.mint m hm).gear
  have coeffFee:f s i l I ≤ v (L.clock.J (m+1)) I:=by
    apply (le_abs_self _).trans
    apply (single_le_sum (f:=fun j:Fin (s+1)=>|f s i j I|) (fun _ _=>abs_nonneg _) (mem_univ l)).trans
    apply (single_le_sum (f:=fun j:Fin (s+1)=>∑k:Fin (s+1),|f s j k I|) (fun _ _=>sum_nonneg (fun _ _=>abs_nonneg _)) (mem_univ i)).trans
    exact single_le_sum (f:=fun u=>∑j:Fin (u+1),∑k:Fin (u+1),|f u j k I|)
      (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>abs_nonneg _))) (mem_range.mpr (Nat.lt_succ_of_le active))
  have priced:=sale s i l Q m hm (coeffFee.trans cash) N live
  rw [draws,coupling,clock] at priced
  suffices raised:zz L m ^ (d s i l) ≤ (max 1 |zz L m|)^(D s) by exact priced.trans raised
  apply (le_abs_self _).trans
  rw [abs_pow]
  apply (pow_le_pow_left₀ (abs_nonneg _) (le_max_right ..) _).trans
  apply pow_le_pow_right₀ (le_max_left ..)
  exact (single_le_sum (f:=d s i) (fun _ _=>Nat.zero_le _) (mem_univ l)).trans
    (single_le_sum (f:=fun j:Fin (s+1)=>∑k:Fin (s+1),d s j k) (fun _ _=>Nat.zero_le _) (mem_univ i))

end YM.Integration.WilsonPositionProgramMeasuredClockTariff
end
