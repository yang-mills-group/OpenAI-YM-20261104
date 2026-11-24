import YM.Integration.WilsonTrueProjectedLocatedWord
import YM.Extra.SOURCE_HISTORIES.Beside

/-! Assemble a finite numerical trial at its real coarse site, keeping each
native hard key and the actual unnormalized original vacuum in the push. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedBasis
open MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Graces Roost
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {d N p i : ℕ}
local notation "C₀" => R.family
local notation "S₀" => R.family.localSection d
local notation "F₀" => R.family.labels.level d
local notation "hi" => R.family.side (i+1) p
local notation "lo" => R.family.side i p

def table {A X : Type*} [Fintype A] (fields : A → X → ℂ) (x : A → ℂ) (U : X) : ℂ :=
  ∑ a, x a*fields a U

theorem push {A : Type*} [Fintype A] (F : A → Config G hi → ℂ) (x : A → ℂ)
    (income : ∀ a, Integrable (F a) (prior G _)) :
    transition (C:=C₀) d N p i (table F x)=
    table (fun a => transition (C:=C₀) d N p i (F a)) x := by
  funext V
  let op := (C₀).path.levels.clock.op i p
  let β := ((C₀).path.rep N p (i+1)).beta
  let L : ℂ := ((C₀).S.block i).val
  have ints (a : A) : Integrable (fun W => op.density β W V • F a W) (prior G _) :=
    StepData.push_slice ((C₀).path.levels.transition_mass i p β) V (F a) (income a)
  change L^d*(∫ W, op.density β W V • (∑ a,x a*F a W) ∂prior G _) =
    ∑ a,x a*(L^d*(∫ W,op.density β W V • F a W ∂prior G _))
  have reorder (W : Config G hi) : op.density β W V • (∑ a,x a*F a W) =
      ∑ a,x a • (op.density β W V • F a W) := by
    simp only [Complex.real_smul,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
  simp_rw [reorder]
  rw [integral_finsetSum]
  · simp_rw [integral_smul,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
  · intro a _
    exact (ints a).smul (x a)

def Paid (W : Rep G lo) (o : Site lo) (q : store C₀ d p i) (B : ℝ) : Prop :=
  q.Format o (C₀).params W ∧ q.remBound o W (safety C₀ i) B ∧ (F₀).coeffSize q.x ≤ B

/-- On the real parent's row, cancel the two evaluations of the emitted
student before combining the native accounts. -/
theorem rejoin (W : Rep G lo) (o : Site lo) {σ C Λ δ w : ℝ} (law : W.Lawful σ C Λ δ w)
    (e z : store C₀ d p i) {u v : ℝ} (pe : Paid R W o e u) (pz : Paid R W o z v)
    (input : Config G hi → ℂ) (student lower : Config G lo → ℂ)
    (issued : transition (C:=C₀) d N p i input=student+e.density o S₀ W)
    (filed : student = lower+z.density o S₀ W) :
    ∃ q : store C₀ d p i, Paid R W o q (u+v) ∧
      transition (C:=C₀) d N p i input=lower+q.density o S₀ W := by
  obtain ⟨pf,pr,pc⟩ := pe
  obtain ⟨qf,qr,qc⟩ := pz
  refine ⟨beside e z,⟨(presentation pf pr qf qr).1,(presentation pf pr qf qr).2,?_⟩,?_⟩
  · rw [reckon]
    exact (Size.add (F₀) e.x z.x).trans (add_le_add pc qc)
  · rw [issued,filed,plus law pr qr S₀]
    abel

/-- Reprice each situated basis column at its actual numerical coefficient.
The budget sums every hard row before paying the single original divisor. -/
theorem original {A : Type*} [Fintype A] (anchor : A) (W : Rep G lo) (o : Site lo)
    {σ C Λ δ w : ℝ} (law : W.Lawful σ C Λ δ w)
    (upper : A → Config G hi → ℂ) (lower : A → Config G lo → ℂ)
    (bills : A → ℝ) (x : A → ℂ) (income : ∀ b, Integrable (upper b) (prior G _))
    (receipts : ∀ b, ∃ q : store C₀ d p i, Paid R W o q (bills b) ∧
      transition (C:=C₀) d N p i (upper b)=lower b+q.density o S₀ W) :
    ∃ q : store C₀ d p i, Paid R W o q (∑ b, ‖x b‖*bills b) ∧
      transition (C:=C₀) d N p i (table upper x)=table lower x+q.density o S₀ W := by
  classical
  choose q paid agree using receipts
  letI : Nonempty A := ⟨anchor⟩
  let entry (b : A) := stretch (x b) (q b)
  let combined := Extra.Histories.merge (code A) entry
  have pos : 0 < safety (C₀) i := by
    obtain ⟨_,_,_,_,_,hk,_,_⟩ := (paid anchor).2.1
    exact hk
  have fees (b : A) := stretch_rem (x b) (paid b).2.1
  have rem := (merge_budget (code A) entry pos fees (hasSum_fintype _).summable).1
  refine ⟨combined,⟨merge_format (code A) entry (fun b => stretch_format (x b) (paid b).1),?_,?_⟩,?_⟩
  · simpa only [tsum_fintype] using rem
  · change (F₀).coeffSize (∑' b, (entry b).x) ≤ _
    rw [tsum_fintype]
    apply (Size.finite (F₀) Finset.univ _).trans
    apply Finset.sum_le_sum
    intro b _
    change (F₀).coeffSize (x b • (q b).x) ≤ _
    rw [Size.smul]
    exact mul_le_mul_of_nonneg_left (paid b).2.2 (norm_nonneg _)
  · rw [push R _ _ income]
    funext U
    have sum := (merge_density (code A) entry pos law fees (hasSum_fintype _).summable
      (hasSum_fintype _).summable S₀ U).tsum_eq.symm
    rw [tsum_fintype] at sum
    have values : combined.density o S₀ W U=∑ b,x b*(q b).density o S₀ W U :=
      sum.trans (Finset.sum_congr rfl fun b _ => stretch_density S₀ W o (x b) (q b) U)
    change table (fun b => transition (C:=C₀) d N p i (upper b)) x U =
      table lower x U + combined.density o S₀ W U
    simp only [table,agree,Pi.add_apply,mul_add,Finset.sum_add_distrib,values]

end YM.Integration.WilsonTrueProjectedLocatedBasis
