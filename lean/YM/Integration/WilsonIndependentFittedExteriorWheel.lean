import YM.Integration.WilsonIndependentFittedExteriorProfile

/-! The real derivatives on the integer root and common center of the finite
experiment, with their normalized home test and exact native child. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorWheel
open Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonIndependentFittedExteriorProfile (home jet paid)
open scoped Topology Classical
variable {D:ℕ}

def row (φ:Rarity D)(ρ:ℝ)(pos:0<ρ)(ξ:Point4)(ε L T:ℝ)(k:Cover)(o:CellR):Volume D:=
  wheelC (ε/T) (L/T) k (home φ ρ pos (T⁻¹ • ξ)).ψ o

theorem address_at (ε L T:ℝ)(k:Cover)(o:CellR)(u:Point4):
    address (ε/T) (L/T) o k u=T⁻¹ • address ε L o k u:=by
  ext b
  simp only [address,Mer.position,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem original (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(ξ:Point4)(ε L T:ℝ)(k:Cover)(o:CellR)(w:Knob D)(u:Chamber):
    (row φ ρ p ξ ε L T k o).val w u =
      (ε/T)^w.1.val*(ρ⁻¹^4*(ρ⁻¹^w.1.val*
        crease φ.ψ w.2 ((T*ρ)⁻¹ • (address ε L o k u.val-ξ)))):=by
  change crease (sonal _ _ _ _ _) w.2 u.val=_
  rw [currentP _ _ _ _ _ _ (Nat.le_of_lt_succ w.1.isLt),jet _ _ p _ _ (Nat.le_of_lt_succ w.1.isLt),
    address_at]
  have rule (x:Point4):ρ⁻¹ • (-(T⁻¹ • ξ)+T⁻¹ • x)=(T*ρ)⁻¹ • (x-ξ):=by
    rw [←smul_neg,←smul_add,smul_smul,mul_inv_rev,sub_eq_neg_add]
  rw [rule]

theorem bound (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(ξ:Point4)(ε L T:ℝ)(k:Cover)(o:CellR)
    (A:ℝ)(bill:Amplitude φ A)(hp:0 ≤ ε/T)(fine:ε/T ≤ 1):
    ‖row φ ρ p ξ ε L T k o‖≤ ρ⁻¹^4*((max 1 ρ⁻¹)^D*A):=
  amplitudes_bound _ _ (paid _ _ p _ _ bill) hp fine _ _

theorem uniform (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(ξ:Point4)(ε L T:ℝ)(k:Cover)(o:CellR)
    (A:ℝ)(bill:Amplitude φ A)(hp:0 ≤ ε/T)(fine:ε/T ≤ 1)(M:ℝ)(base:1 ≤ M)(near:ρ⁻¹ ≤ M):
    ‖row φ ρ p ξ ε L T k o‖≤ M^(D+4)*A:=by
  have nn:=bill.1
  have hρ:0 ≤ ρ⁻¹:=(inv_pos.mpr p).le
  have hM:0 ≤ M:=zero_le_one.trans base
  have both:0 ≤ max 1 ρ⁻¹:=zero_le_one.trans (le_max_left ..)
  calc ‖_‖ ≤ _:=bound φ ρ p ξ ε L T k o A bill hp fine
       _ ≤ M^4*(M^D*A):=mul_le_mul
          (pow_le_pow_left₀ hρ near _) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ both (max_le base near) _) nn)
          (mul_nonneg (pow_nonneg both _) nn) (pow_nonneg hM _)
       _=M^(D+4)*A:=by rw [pow_add];ring

theorem child (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(ξ:Point4)(ε L T:ℝ)(P:Patch)(k:Cover)(o:CellR)(a:Site P.L):
    foldWord P a D (row φ ρ p ξ (ε*P.L.val) L T k o)=row φ ρ p ξ ε L T (P.L.val • k+lift a) o:=by
  change foldWord P a D (page D (sonal _ _ _ _ _))=page D _
  rw [observed,show (ε*P.L.val)/T=(ε/T)*P.L.val from by ring,growingP]

end YM.Integration.WilsonIndependentFittedExteriorWheel
