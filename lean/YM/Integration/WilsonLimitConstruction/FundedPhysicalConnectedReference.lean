import YM.Integration.LocalComparisonVacuumRemainder
import YM.Integration.ActualCoveredNormalization
import YM.Next.RANK.Exponential

/-! The genuine finite connected comparison at every field, including fields
with nonempty forced gas. Its marked coefficients are determined by the
original physical readout divided by the original positive finite density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPhysicalConnectedReference
open Lattice Wilson RG RG.Supply Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic
open LocalComparison Next.Rank.Exponential
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V X : Type} [Fintype V] [DecidableEq V]
    {Γ : Census V} {P : Rep G n} {o : V→Site n} (T : Taste X o P Γ)

structure Actual where
  positive (U : Config G n) : 0<P.eval U
  vacuum (x : X) (U : Config G n) : ((T.leaf x).density U).part Γ.quiet=(P.eval U:ℂ)
  gas (U : Config G n) : Summable (fun f : Finset ℕ => ‖P.activities.gasOccurrence P.p f U‖)

theorem paid {δ k : ℝ} (valid : P.activities.Valid P.p δ k) (positive : ∀U,0<P.eval U)
    (act : ∀x,(T.leaf x).Active)
    (funded : ∀x, ∃ (w : V→ℝ) (u a d b c : ℝ), (T.leaf x).Budget w u a d b c) : Actual T where
  positive := positive
  vacuum x U := by
    obtain ⟨w,u,a,d,b,c,h⟩ := funded x
    exact (T.leaf x).vacuum (act x) h valid U
  gas := (Activities.gasSeries valid).absolute

theorem from_purchase {δ k : ℝ} (valid : P.activities.Valid P.p δ k) (positive : ∀U,0<P.eval U)
    {w : V→ℝ} {u a d b c : ℝ} (h : T.Snacks w u a d b c) : Actual T :=
  paid T valid positive (fun x => (T.snack h x).1)
    (fun x => ⟨w,u,a,d,b,c,(T.snack h x).2⟩)

def normalized (x : X) (U : Config G n) : Poly Γ :=
  ((P.eval U:ℂ)⁻¹) • (T.leaf x).density U

variable (H : Actual T)

include H in
theorem unit (x : X) (U : Config G n) : (normalized T x U).part Γ.quiet=1 := by
  have h : (P.eval U:ℂ)≠0 := by exact_mod_cast (H.positive U).ne'
  rw [normalized,Poly.part_smul,H.vacuum,inv_mul_cancel₀ h]

def source (x : X) (U : Config G n) : Poly Γ :=
  connected (normalized T x U) (unit T H x U)

theorem expansion (x : X) (U : Config G n) :
    Expands (source T H x U) (normalized T x U) :=
  connected_spec _ _

theorem unique (x : X) (U : Config G n) (r : Poly Γ) (hq : r.part Γ.quiet=0)
    (physical : (T.leaf x).density U=(P.eval U:ℂ) • Poly.pass r) : r=source T H x U := by
  refine Expands.uniq (F:=normalized T x U) ?_ (expansion T H x U)
  refine ⟨hq,?_⟩
  have h : (P.eval U:ℂ)≠0 := by exact_mod_cast (H.positive U).ne'
  rw [normalized,physical,inv_smul_smul₀ h]

theorem formal (x : X) (U : Config G n) :
    (T.leaf x).density U=(P.eval U:ℂ) • Poly.pass (source T H x U) := by
  have h : (P.eval U:ℂ)≠0 := by exact_mod_cast (H.positive U).ne'
  rw [(expansion T H x U).2,normalized,smul_smul,mul_inv_cancel₀ h,one_smul]

theorem full (x : X) (U : Config G n) :
    (T.leaf x).density U=Poly.pass (source T H x U)*((vacuumRemainder T).leaf x).density U := by
  rw [vacuumRemainder_density T x U (H.gas U),mul_smul_comm,mul_one]
  exact formal T H x U

theorem ordinary (x : X) (U : Config G n) :
    (T.leaf x).log U=(T.leaf x).log U+((vacuumRemainder T).leaf x).log U := by
  rw [vacuumRemainder_log,add_zero]

end YM.Integration.WilsonLimitConstruction.FundedPhysicalConnectedReference
end
