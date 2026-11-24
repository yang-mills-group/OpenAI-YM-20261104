import YM.Integration.WilsonCapturedPrimaryCourse
import YM.Integration.WilsonRegisteredLogFare
import YM.Extra.SOURCE_HISTORIES.Issue

/-! The fixed local section in the original file is readable on each reissue
of that date's genuine budget. The same column fee is uniform in N and per. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySection
open Filter Lattice Wilson RG Source Labels Next.Foundations Push.Local Extra.Histories
open PhysicalNext.Repeat.Legato Pert.Asymptotics RG16
open scoped Classical Topology

variable {G : Gauge} (R : Run G)

theorem original {d i per : ℕ} (date : R.t d ≤ i) (P : RG.Rep G (R.family.side i per))
    (budget : P.p = R.family.path.levels.budget i) :
    Readable (hol G) (localSection G d) P.p (R.family.side i per)
      (R.family.path.levels.params i).columns ∧ d+1 ≤ P.p.order := by
  let issued := Issue.refer R.family.path R.w R.y R.t R.b.clock R.accepts
  have rank := (issued.order d).2 i date
  rw [budget]
  exact ⟨⟨issued.gets d,issued.fits d i per date,(Nat.le_succ d).trans rank.1,rank.2,
    issued.loaded d i date,zero_le_one.trans (R.family.path.levels.params i).columns_ge⟩,rank.1⟩

theorem priced (simple : G.Simple)
    (slow : ∀ m, ((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m)) :
    ∀ᶠ i:ℕ in atTop, ∀ N per, i<N →
      (R.family.path.levels.params i).columns ≤ 4/(regulatorRun R.family N per (i+1))^2 := by
  let A := R.family.path.levels
  obtain ⟨first,hfirst⟩ := eventually_atTop.mp (WilsonRegisteredLogFare.column R simple slow)
  refine eventually_atTop.mpr ⟨first+1,fun i d N per live => ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
  have columns := hfirst j (by omega)
  have stops := WilsonAdmissionScale.logarithm_monotone A simple (Nat.le_succ (j+1))
  have log := Real.log_le_self (le_trans zero_le_one (A.fits.delayed (j+2)).le)
  let β := (R.family.path.rep N per (j+2)).beta
  have band := (R.makes.wilson.represents N per (j+2) live).band.1
  change A.clock.hatBeta (j+2)/2 ≤ β at band
  have pos : 0<β := RG02.Actual.coupling_pos R.makes.wilson live
  have value : 4/(regulatorRun R.family N per (j+2))^2 = 4*β := by
    change 4/(Real.sqrt β)⁻¹^2 = 4*β
    rw [inv_pow,div_inv_eq_mul,Real.sq_sqrt pos.le]
  rw [value]
  calc
    _ ≤ 2*Real.log (A.clock.hatBeta (j+2)) := columns.trans (mul_le_mul_of_nonneg_left stops (by norm_num))
    _ ≤ 2*(A.clock.hatBeta (j+2)) := mul_le_mul_of_nonneg_left log (by norm_num)
    _ ≤ _ := by linarith only [band]

end YM.Integration.WilsonCapturedPrimarySection
