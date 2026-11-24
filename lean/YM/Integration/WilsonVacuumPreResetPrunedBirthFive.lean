import YM.Integration.WilsonVacuumPreResetPrunedBirthCover
import YM.Integration.WilsonLimitConstruction.FundedGeometryNonwrap
import YM.RG01Estimate.Yonder

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedBirthFive
open Function Set Lattice RG RG.Shoot Pressure Wilson WilsonStartup
open PhysicalNext PhysicalNext.Repeat Legato RG01Estimate
open WilsonVacuumPreResetPrunedBirthSites WilsonVacuumPreResetPrunedBirth
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(archive:Extension.UV.Archive R.alloy.B)(m per:ℕ)
set_option quotPrecheck false
local notation "a" => R.alloy.B.a
local notation "H" => ((a).S.oneStep m per).exact_size
local notation "Y" => R.family.path.rep (m+1) per (m+1)

include archive
theorem physical (hm:1 ≤ m)(ℓ d:ℕ)(hd:3≤d):
    ∃A:Board.Insured R.alloy (m+1) m d (H) (Y).beta Shapes,
      A.rep.eval=(Y).eval ∧ Inherit.Debits A.rep A.sacrifice 0 ∧
      ∃C:∀i:Fin 5,Board.Insured R.alloy (m+1) m d (Precise.starlet R.alloy m ℓ i) (Y).beta Shapes,
      (∀i, (C i).rep.eval=bare (Y).beta ∧ Inherit.Debits (C i).rep (C i).sacrifice 0 ∧
        Board.Clockset (H) (Precise.starlet R.alloy m ℓ i) (Y).beta A (C i)) ∧
      ∀i j,Board.Clockset (Precise.starlet R.alloy m ℓ i) (Precise.starlet R.alloy m ℓ j)
        (Y).beta (C i) (C j):=by
  have hb: (Y).beta∈band (a) (m+1):=(R.makes.wilson.represents (m+1) per (m+1) le_rfl).band
  have large:2 ≤ ((a).S.side m per).val:=by
    have growth:=WilsonLimitConstruction.FundedGeometryNonwrap.side (a).S m per
    have first:3^1 ≤ 3^m:=Nat.pow_le_pow_right (by omega) hm
    omega
  have fence (i:Fin 5):2 ≤ (Precise.shape R.alloy m ℓ i).val:=by
    rw [Precise.shape_ack];unfold Trio.tent;omega
  refine ⟨paid R archive m (H) (Y).beta hb d hd,?_,zero_debt ..,
    fun i=>paid R archive m (Precise.starlet R.alloy m ℓ i) (Y).beta hb d hd,?_,?_⟩
  · exact (funext (WilsonVacuumPreResetPrunedBirth.measured R archive m (H) (Y).beta hb d hd)).trans
      (R.makes.wilson.starts (m+1) per).2.symm
  · intro i
    exact ⟨funext (measured R archive m (Precise.starlet R.alloy m ℓ i) (Y).beta hb d hd),
      zero_debt ..,WilsonVacuumPreResetPrunedBirthCover.original R archive m _ _ _ hb d hd large (fence i)⟩
  · intro i j
    exact WilsonVacuumPreResetPrunedBirthCover.original R archive m _ _ _ hb d hd (fence i) (fence j)

end YM.Integration.WilsonVacuumPreResetPrunedBirthFive
