import YM.Integration.FullQLocalProducedOutput
import YM.Integration.LocalComparisonBlockSupport
import YM.Next.RANK.Exponential

/-! The independent cover model can differ from the finite one in every
marked coefficient. Reassign its true signed difference between the formal
and residual sources of the original complete tested density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCoverMarkedCorrection
open Function Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories OPE.Therm
open RG3.Script.Picnic LocalComparison FullQLocal
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    {C : Family G} {Γ : Census V} {D : V → ComparisonDensity.Address.Orbit}
    {N p m : ℕ} {Q : PhysicalCarrier C N p (m+1)}
    {o : V → Site (C.side (m+1) p)} {o' : V → Site (C.side m p)}
    {input : Taste (TestSpace D) o Q.rep Γ} (O : ProducedOutput D Q o o' input)
    (cover : MarkedPackets D G (C.side m p) Γ)

local notation "g₀" => Pert.Asymptotics.regulatorRun C N p (m+1)

/-- This full signed difference is defined from the two original models
on the same configuration and the same complete independent tests. -/
def difference (x : TestSpace D) (U : Config G (C.side m p)) : Poly Γ :=
  O.model.read x g₀ U-cover.read x g₀ U

theorem quiet (x : TestSpace D) (U : Config G (C.side m p)) :
    (difference O cover x U).part Γ.quiet=0 := by
  rw [difference,Next.Rank.Exponential.part_sub,O.model.quiet_read,cover.quiet_read,sub_self]

theorem finite (x : TestSpace D) (U : Config G (C.side m p)) :
    Poly.pass (O.model.read x g₀ U)=Poly.pass (cover.read x g₀ U)*Poly.pass (difference O cover x U) := by
  rw [←Next.Rank.Exponential.pass_add _ _ (cover.quiet_read x _ U) (quiet O cover x U)]
  congr 1
  unfold difference
  abel

theorem covering (x : TestSpace D) (U : Config G (C.side m p)) :
    Poly.pass (cover.read x g₀ U)=Poly.pass (-difference O cover x U)*Poly.pass (O.model.read x g₀ U) := by
  rw [←Next.Rank.Exponential.pass_add _ _ (by rw [Poly.part_neg,quiet,neg_zero]) (O.model.quiet_read x _ U)]
  congr 1
  unfold difference
  abel

/-- The physical marked winding correction carries its own two actual
finite activities. Its ordinary logarithm may differ from the whole
marked logarithm through the original compulsory clusters. -/
structure Realization where
  formal : Taste (TestSpace D) o' O.carrier.rep Γ
  residual : Taste (TestSpace D) o' O.carrier.rep Γ
  ordinary : TestSpace D → Config G (C.side m p) → Poly Γ
  formal_density (x U) : (formal.leaf x).density U=
    Poly.pass (-difference O cover x U)*(O.formalAligned.leaf x).density U
  residual_density (x U) : (residual.leaf x).density U=
    Poly.pass (difference O cover x U)*(O.residual.leaf x).density U
  formal_log (x U) : (formal.leaf x).log U=(O.formalAligned.leaf x).log U-ordinary x U
  residual_log (x U) : (residual.leaf x).log U=(O.residual.leaf x).log U+ordinary x U

def produced (S : Realization O cover) : ProducedOutput D Q o o' input where
  carrier := O.carrier
  model := cover
  output := O.output
  residual := S.residual
  formalAligned := S.formal
  roots := O.roots
  vacuum := O.vacuum
  density := O.density
  full x U := by rw [O.full,finite O cover,S.residual_density,mul_assoc]
  formal_full x U := by rw [S.formal_density,O.formal_full,covering O cover,mul_smul_comm]
  regular_log x U := by rw [O.regular_log,S.formal_log,S.residual_log]; abel

/-- The physical normalized residual and its finite winding correction
multiply before one takes any relative estimate. -/
theorem relative (S : Realization O cover) (x : TestSpace D) (U : Config G (C.side m p)) :
    (produced O cover S).residualError x U =
      Poly.pass (difference O cover x U)*O.residualError x U+
        (Poly.pass (difference O cover x U)-1) := by
  change ((C.path.rep N p m).eval U)⁻¹ • (S.residual.leaf x).density U-1=_
  rw [S.residual_density,←mul_smul_comm]
  unfold ProducedOutput.residualError
  ring

end YM.Integration.WilsonLimitConstruction.FundedCoverMarkedCorrection
end
