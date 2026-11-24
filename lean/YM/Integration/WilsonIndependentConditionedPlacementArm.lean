import YM.Integration.WilsonIndependentConditionedBankRulerPorts
import YM.Integration.WilsonReflectedMixedObservedArms

/-! The authenticated seed on the original reporting ruler is fixed by the original public enrollment, including its orientation and engineering units, independently of its lattice location. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPlacementArm
open Function Finset Lattice RG Wilson Source Labels Extra.Histories
open XSpace XSpace.Rose XSpace.Cirrus PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain PowerSeries
open WilsonIndependentConditionedBankSeats (Resident raw)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonAddressedTrialPivotUnits (row)
open WilsonReflectedMixedObservedArms (Printed)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentConditionedBankRankedPorts (offered incoming)
open WilsonIndependentConditionedBankRulerPorts (rehome)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){d D f K N per m j target:ℕ}{up:f≤K}{live:K≤N}{η:ℝ}
local notation "F" => R.family.labels.level d
local notation "a" => R.family.S.a
variable (axes:R.family.label d≃ₗ[ℂ]R.family.label d)(source:R.family.label d)(turn:Signed)(hand:Bool)(phase:ℂ)

def head (d j K N per:ℕ)(axes:R.family.label d≃ₗ[ℂ]R.family.label d)(source:R.family.label d)
    (turn:Signed)(hand:Bool)(phase:ℂ): (R.family.labels.level d).Coeff:=
  row R d K N per phase (Motion.patch (R.family.labels.level d) (turn,hand) (axes.symm (fitted R d j N per source)))

def stencil (j m f K N per:ℕ)(I:Initialize G)(survey plain im:Bool)(fit:d<D):TowerS G D:=
  Shrine (plate (sectionAt R I survey d) fit)
    (((a f/a m)^d) • offered F plain im (((a K/a f)^d) • head R d j K N per axes source turn hand phase))

variable (v:Resident R d f K N per target up live η){loc:Site (R.family.side f per)}
variable (placed:Printed R j axes source turn hand loc v.arm)(phased:v.phase=phase)

include placed phased

theorem original:raw v=head R d j K N per axes source turn hand phase:=by
  rw [raw,coords,head,phased,placed.rotation,placed.hand,placed.inverse]

theorem filed (I:Initialize G)(survey plain im:Bool)(fit:d<D):
    Shrine (plate (sectionAt R I survey d) fit) (rehome v m plain im)=
      stencil R axes source turn hand phase j m f K N per I survey plain im fit:=by
  rw [stencil,rehome,incoming,original R axes source turn hand phase v placed phased]

end YM.Integration.WilsonIndependentConditionedPlacementArm
