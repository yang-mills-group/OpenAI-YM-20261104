import YM.Integration.WilsonVacuumPreResetOriginalOutput
import YM.Integration.WilsonVacuumPreResetFoldedInlet

/-! Original funded deposited input, chosen before every period and
forest, with its whole signed finite conditional vacuum output. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFundedOutput
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

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,
      let A:=levels R
      ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz A (m+1) ∧ ∀N:ℕ,m<N→
        let C:=W.buy (zz A (m+1))+zz A (m+1)*A.clock.loopCap (m+1)
        ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
          Z.length ≤ meterPre (3+e) ∧ Draw Z σ C ∧
          ∀(p:ℕ)(F:Forest (step R m p).ratio)(tag:(step R m p).Choices)
            {T:Type} [DecidableEq T] [Fintype T] {J:Census T} (Q:Bulk.Colors J G (fine R m p))
            (x y:fieldDir G (coarse R m p) 1)(t:ℕ)(_read:t≤e+2)(live:m<N),
          held R N m p live F tag Z Q (e+2) x (e+2) t-held R N m p live F tag Z Q (e+2) y (e+2) t=
            -(diff (output R N m p) t (flatten x) (flatten y):ℂ):=by
  obtain ⟨W,dates⟩:=FundedOriginalVacuumPaths.corrections R simple v rows paths e
  obtain ⟨m₀,hm₀⟩:=eventually_atTop.1 dates
  refine ⟨W,eventually_atTop.2 ⟨m₀,?_⟩⟩
  intro m hbase A
  obtain ⟨early,good,fee,work⟩:=hm₀ (m+1) (by omega)
  refine ⟨_,good,fee,?_⟩
  intro N live C
  obtain ⟨Z,born,ends,size,draw,store⟩:=work N live
  refine ⟨Z,born,ends,size,draw,?_⟩
  intro p F tag T _ _ J Q x y t ht _
  let U:=filed R N m p Z
  let E:=covered R N m p
  have kp:(income R N m p).path=R.alloy.B.kin.path N (m+1):=(RunFormalChain.fromRun R).selected N p (m+1) live
  have kb:(income R N m p).clip=((levels R).params (m+1)).clip:=(RunFormalChain.fromRun R).clips N p (m+1) live
  have filedRows (a:ℕ)(ha:a<3+e)(l:ℕ):U a (l+1)=E a (l+1):=by
    unfold U filed
    rw [kp,kb]
    exact (store a ha).2 (fine R m p) l
  have head:=WilsonVacuumPreResetDepositedPhase.head R N m p live Z simple (filedRows 0 (by omega))
  have price (a:ℕ)(ha:a<3+e):coeff a (Blue.flash U-Blue.flash E)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff a (Blue.flash U-Blue.flash E))):=
    WilsonVacuumPreResetFoldedInlet.fieldIndependent U E a
      (WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _) (filedRows a ha)
  exact WilsonVacuumPreResetOriginalOutput.original R N m p live F tag Z head Q ((levels R).budget (m+1))
    (e+2) good draw born (fun a ha=>by have h:=ends a ha; omega) simple (3+e) price x y (e+2) t ht (by omega)

end YM.Integration.WilsonVacuumPreResetFundedOutput
