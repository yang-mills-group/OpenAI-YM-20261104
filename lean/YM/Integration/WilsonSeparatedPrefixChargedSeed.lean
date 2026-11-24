import YM.Integration.WilsonAddressedFiniteGuardTrial
import YM.Integration.WilsonReflectedPublicTrialRoster
import YM.Integration.WilsonSeparatedPrefixScreenedWord
import YM.Integration.WilsonMovingForkHeterogeneousCut

/-! The occupied K print and the physical N product share the same scalar on every group configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixChargedSeed
open Function Finset Set Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal PertExtension PertExtension.LatticePT
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonOriginalTwoFlatGridCapture WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n → ℕ){N p K f:ℕ}
local notation "C" => R.family

theorem printed (live:K≤N)(ξ:Fin n → Site ((C).side K p))(w:∀i,(C).label (d i))(c:Fin n→ℂ):
    WilsonAddressedFiniteGuardTrial.printed R d (N:=N) ξ w (WilsonReflectedPublicTrialRoster.factor R K d c)
      WilsonOriginalAlternativeFiniteSource.fired (Stock.final (Fin n))=
        fun U=>(∏i,c i)*product R d (N:=N) ξ w U:=by
  funext U
  change (∏i,∑l,entire R (d i) K (N,p) _ l*WilsonPositionProgramBlockedTrialFiling.atomAt R (d i) N p K (ξ i) l U)=_
  unfold product
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl;intro i _
  rw [WilsonPositionProgramBlockedTrialFiling.filed R (d i) N p K live (ξ i),Finset.mul_sum]
  apply Finset.sum_congr rfl;intro l _
  simp only [entire,gMap,Frame.scaled_apply,units,submitted,WilsonOriginalAlternativeFiniteSource.fired,
    WilsonReflectedPublicTrialRoster.factor,one_mul,Pi.smul_apply,smul_eq_mul]
  ring

theorem physical (live:f≤N)(site:Fin n→ Cover)(Y:∀i,(C).label (d i))(c:Fin n→ℂ):
    (fun U=>∏a∈(Stock.final (Fin n)).val,c a * (C).O N p
      (WilsonReflectedPublicOrientedFaces.displayed R (d a) (Y a) (1,false))
      (anchorAt R (snap (C) f p site a) N) U)=fun U=>(∏a,c a)*word R d f N p live site Y U:=by
  have full:=WilsonSeparatedPrefixScreenedWord.original R (p:=p) d live site Y
  funext U
  rw [Finset.prod_mul_distrib,←congrFun full U]
  rfl

end YM.Integration.WilsonSeparatedPrefixChargedSeed
end
