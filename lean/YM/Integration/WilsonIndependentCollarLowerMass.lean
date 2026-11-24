import YM.Integration.WilsonOriginalCensusDatedPeriodOpening
import YM.Integration.WilsonIndependentCollarDatedMaterial

/-! Pay the actual lower winding receiver before the period from the
ordinary direction on its one common test; the only multiplicity is
the finite number of actual copies posted with exactly that mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarLowerMass
open Finset Function Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza QuadraticLocal Multi Marker
open WilsonOriginalCensusDatedMaterial
open WilsonOriginalCensusDatedHeldTariff (salary)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I]{n e N j:ℕ}{k:Fin n→ℕ}{side:Side}{σ:ℝ}
  {P:Earn.Passport side (Fin n)}{R:Run G}{B:I→Earn.Binder P (Stock.census (Fin n))}
  (H:Material R N j e k σ B)(x:Affinity.Wallet (room (Fin n)))(s:(Stock.census (Fin n)).Mode)

def copies (B:I→Earn.Binder P (Stock.census (Fin n)))(s:(Stock.census (Fin n)).Mode):ℕ:=
  (univ.filter fun z=>(B z).mode=s).card

theorem charge (t:Case H.tests)(fixed:∀z,H.source z=t):
    salary H x s=(copies B s:ℝ)*(‖∏v∈s.val,(x v).val‖*‖touch t s.val‖):=by
  unfold salary copies
  calc
    _=∑z:I,if (B z).mode=s then ‖∏v∈s.val,(x v).val‖*‖touch t s.val‖ else 0:=by
      apply sum_congr rfl
      intro z _
      by_cases h:(B z).mode=s
      · rw [if_pos h.symm,if_pos h,fixed z,h]
      · rw [if_neg (Ne.symm h),if_neg h]
    _= _:=by rw [←sum_filter];simp [nsmul_eq_mul]

theorem cartesian {D:Fin n→ℕ}(t:Case D)(J:Finset (Fin n)):
    ‖touch t J‖ ≤ ∏v∈J,‖t v‖:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (prod_nonneg fun _ _=>norm_nonneg _)
  intro v
  rw [hit_leaf,mul_comm]
  exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left (folio_norm t) (norm_nonneg _))

theorem unique (disjoint:Injective fun z=>(B z).mode):copies B s≤1:=by
  apply card_le_one.mpr
  intro a ha b hb
  exact disjoint ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)

theorem original (t:Case H.tests)(fixed:∀z,H.source z=t)(cap:ℕ)(admitted:copies B s≤cap):
    salary H x s≤cap*(∏v∈s.val,‖(x v).val‖*‖t v‖):=by
  rw [charge H x s t fixed, Finset.prod_mul_distrib, norm_prod]
  exact mul_le_mul (by exact_mod_cast admitted)
    (mul_le_mul_of_nonneg_left (cartesian t s.val) (prod_nonneg fun _ _=>norm_nonneg _))
    (mul_nonneg (prod_nonneg fun _ _=>norm_nonneg _) (touch t s.val).opNorm_nonneg) (Nat.cast_nonneg _)

end YM.Integration.WilsonIndependentCollarLowerMass
end
