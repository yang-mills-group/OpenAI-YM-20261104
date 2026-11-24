import YM.Integration.WilsonOriginalMicroscopicEntrancePeerSchool

/-! The two genuine companion apertures remove the weights on a three-name
flat hearing. The nominated arm itself is excluded from the product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePairRefund
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonMeasuredCompanionWage
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)

theorem original {χ V X:ℝ}(w:Fin 3→ℝ)(ℓ q:ℕ)(one:1≤χ)(vp:0≤V)(pos:∀a,0<w a)
    (aperture:∀a,(w a)⁻¹≤χ^ℓ)(a:Fin 3)(s:(J).Mode)
    (bill:companions a (Stoop.radius w 2) s*X≤(χ^(q+2*ℓ))⁻¹*V):
    X≤4*(χ^q)⁻¹*V:=by
  have hp:0<χ:=zero_lt_one.trans_le one
  have grow:1≤χ^ℓ:=one_le_pow₀ one
  have cutoff:1≤2*χ^ℓ:=by linarith only [grow]
  have crop (i:Fin 3):0<Stoop.radius w 2 i:=div_pos (pos i) (by norm_num)
  have rad:0<companions a (Stoop.radius w 2) s:=Finset.prod_pos (fun i _=>crop i)
  have shoot (i:Fin 3):(Stoop.radius w 2 i)⁻¹≤2*χ^ℓ:=by
    change (w i/(2:ℝ))⁻¹≤_
    rw [inv_div,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (aperture i) (by norm_num)
  have count:(s.val.erase a).card≤2:=by
    calc
      _ ≤ (Finset.univ.erase a).card:=by
        apply Finset.card_le_card
        intro i h
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,Finset.mem_univ i⟩
      _ = 2:=by simp
  have inverse:(companions a (Stoop.radius w 2) s)⁻¹≤(2*χ^ℓ)^2:=by
    unfold companions
    rw [←Finset.prod_inv_distrib]
    calc
      _ ≤ ∏ i∈s.val.erase a,(2*χ^ℓ):=Finset.prod_le_prod (fun i _=>(inv_pos.mpr (crop i)).le) (fun i _=>shoot i)
      _ = (2*χ^ℓ)^(s.val.erase a).card:=by simp
      _ ≤ _:=pow_le_pow_right₀ cutoff count
  calc
    X = (companions a (Stoop.radius w 2) s)⁻¹*(companions a (Stoop.radius w 2) s*X):=by field_simp [rad.ne']
    _ ≤ (2*χ^ℓ)^2*((χ^(q+2*ℓ))⁻¹*V):=(mul_le_mul_of_nonneg_left bill (inv_nonneg.mpr rad.le)).trans
        (mul_le_mul_of_nonneg_right inverse (mul_nonneg (inv_nonneg.mpr (pow_nonneg hp.le _)) vp))
    _ = _:=by
      rw [Nat.mul_comm 2 ℓ,pow_add,pow_mul,mul_pow]
      field_simp [hp.ne']
      ring

end YM.Integration.WilsonOriginalMicroscopicEntrancePairRefund
end
