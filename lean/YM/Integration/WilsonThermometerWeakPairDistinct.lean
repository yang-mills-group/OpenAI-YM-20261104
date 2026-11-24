import YM.Integration.WilsonThermometerWeakPairRooms

/-! Genuine separated occupied arms before and after the child contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairDistinct
open Function Finset Filter Set Table Spec OPE OPE.Arboreal
open WilsonThermometerWeakPairFork WilsonThermometerWeakPairRooms
open scoped Classical Topology BigOperators
private theorem gates (X:Fin 5→E4)(h23:X 2≠X 3)(h24:X 2≠X 4)(h34:X 3≠X 4)(h14:X 1≠X 4):
    Injective (crop X frame.leaves) ∧ Injective (beside (crop X near) (sole (X 4))) ∧
      Injective (crop X WilsonThermometerWeakPairRooms.outside) ∧ Injective (beside (sole (X 1)) (sole (X 4))):=by
  have far (i: Fin 5)(hi:i∈near):X i≠X 4:=by
    rcases (by simpa [near] using hi : i=2∨i=3) with rfl|rfl <;> assumption
  refine ⟨?_,beside_distinct.mpr ⟨?_,fun _ _ _=>Subsingleton.elim ..,fun i _=>far i.1 i.2⟩,?_,
    beside_distinct.mpr ⟨fun _ _ _=>Subsingleton.elim ..,fun _ _ _=>Subsingleton.elim ..,fun _ _=>h14⟩⟩
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ h
    change X i=X j at h;apply Subtype.ext
    rcases (by simpa [leave] using hi : i=2∨i=3∨i=4) with rfl|rfl|rfl <;>
      rcases (by simpa [leave] using hj : j=2∨j=3∨j=4) with rfl|rfl|rfl <;> simp_all
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ h
    change X i=X j at h;apply Subtype.ext
    rcases (by simpa [near] using hi : i=2∨i=3) with rfl|rfl <;>
      rcases (by simpa [near] using hj : j=2∨j=3) with rfl|rfl <;> simp_all
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ h
    change X i=X j at h;apply Subtype.ext
    rcases (by simpa [WilsonThermometerWeakPairRooms.outside] using hi : i=1∨i=4) with rfl|rfl <;>
      rcases (by simpa [WilsonThermometerWeakPairRooms.outside] using hj : j=1∨j=4) with rfl|rfl <;> simp_all

theorem actual {r t M s:ℝ}{x y z:E4}(rp:0<r)(rt:r≤t)(sp:0<s)(hx:‖x‖≤M)(hy:‖y‖≤M)
    (hz:2*s≤‖z‖)(xy:s≤‖x-y‖)(gap:r*M≤t*s):
    let X:=WilsonThermometerWeakPairFork.position r t x y z
    Injective (crop X frame.leaves) ∧ Injective (beside (crop X near) (sole (X 4))) ∧
      Injective (crop X WilsonThermometerWeakPairRooms.outside) ∧ Injective (beside (sole (X 1)) (sole (X 4))):=by
  have tp:=rp.trans_le rt
  have away:0<‖z‖:=by linarith
  have stop(a:E4)(mem:‖a‖≤M):r • a≠t • z:=by
    intro eq
    have norm:=congrArg norm eq
    rw [norm_smul,norm_smul,Real.norm_of_nonneg rp.le,Real.norm_of_nonneg tp.le] at norm
    have tight: t*s<t*‖z‖:=mul_lt_mul_of_pos_left (by linarith) tp
    exact tight.not_ge ((norm ▸ mul_le_mul_of_nonneg_left mem rp.le).trans gap)
  apply gates
  · change r • x≠r • y
    intro eq
    have cross:=congrArg (fun a:E4=>r⁻¹ • a) eq
    rw [inv_smul_smul₀ rp.ne',inv_smul_smul₀ rp.ne'] at cross
    rw [cross,sub_self,norm_zero] at xy
    exact sp.not_ge xy
  · exact stop x hx
  · exact stop y hy
  · exact Ne.symm (smul_ne_zero tp.ne' (norm_pos_iff.mp away))
end YM.Integration.WilsonThermometerWeakPairDistinct
end
