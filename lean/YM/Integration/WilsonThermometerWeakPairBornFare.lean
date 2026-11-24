import YM.Integration.WilsonThermometerWeakPairInventory
import YM.Integration.WilsonThermometerWeakRunningRoster
import YM.Integration.WilsonThermometerWeakMovingCorner

/-! Original geometric-weight rental for one true running input, without
replacing its chamber, its orientation or any lower field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairBornFare
open Function Finset Filter Set Table Spec OPE OPE.Prescription EveryPhase OPE.Nesting
open Climb Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace OPE.Log
open WilsonThermometerWeakMovingCorner
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (P:Prescription F.sector.derivatives)
theorem original {simple:G.Simple}{A:Almanac F}(H:Roll.{u} F simple A)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (hp:P.Coherent)(J:ℝ→tower S)(V:Store G)(lead:Leading F J)(d:ℕ)(v:RG17.Free R.family d):
    ∃(B:ℝ)(m:ℕ),0≤B ∧ ∀ᶠ r in trail,
      WilsonThermometerWeakPairInventory.rent P d r (J r d v)≤B*dock r^m:=by
  obtain ⟨C,k,cp,rr⟩:=WilsonThermometerWeakRunningRoster.original F P H agency hp d
  obtain ⟨W,wp,wallet⟩:=WilsonNormalizedReflectedForm.uniform F J V lead d (norm_nonneg v)
  refine ⟨C*W,k,mul_nonneg cp wp,?_⟩
  have small:∀ᶠ u in trail,u≤1:=(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [rr,wallet,small,self_mem_nhdsWithin] with r rent paid top rp
  have live:=rent (J r d v)
  have cost:cost F d r (J r d v)≤W:=paid false v le_rfl
  have positive:0≤C*dock r^k:=mul_nonneg cp (pow_nonneg (zero_le_one.trans (dock_valid r ⟨rp,top⟩)) _)
  exact live.trans ((mul_le_mul_of_nonneg_left cost positive).trans_eq (by ring))
theorem reflected {simple:G.Simple}{A:Almanac F}(H:Roll.{u} F simple A)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (hp:P.Coherent)(J:ℝ→tower S)(V:Store G)(lead:Leading F J)(d:ℕ)(v:RG17.Free R.family d):
    ∃(B:ℝ)(m:ℕ),0≤B ∧ ∀ᶠ r in trail,
      WilsonThermometerWeakPairInventory.rent P d r (far F J d r v).2≤B*dock r^m:=by
  obtain ⟨B,k,bp,paid⟩:=original F P H agency hp J V lead d (reflect d v)
  refine ⟨B,k,bp,?_⟩
  filter_upwards [paid,lead.equivariant d] with r buy eq
  rw [show (far F J d r v).2=J r d (reflect d v) from (PhysMS.Frame.flip_coupled F d J r eq v).symm]
  exact buy
end YM.Integration.WilsonThermometerWeakPairBornFare
end
