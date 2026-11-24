import YM.Integration.WilsonCapturedSignedRemainder
import YM.Trace.Physicalv2.GermChain

/-! A physical counterterm fixed by one true periodic germ is the same
original factory column throughout the earlier reference-to-capture
interval. Its subtraction leaves exactly the original forcing. All
integrability used below is paid by the given original foreground and
the physical shot at capture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedFactoryCocycle
open Function Filter MeasureTheory Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 Push.Local Extra.Histories
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (d N p : ℕ)

def subtract (x : R.family.label d) (err : Er R.family p) : Er R.family p :=
  fun i => err i-calValues (C:=R.family) d N p i x

private theorem column (i : ℕ) (ref : R.family.ref d ≤ i) (stop : i ≤ N) (x : R.family.label d) :
    Integrable (calValues (C:=R.family) d N p i x) (prior G (R.family.side i p)) :=
  message d N p i R.makes ref stop (entryOk d N p i R.makes ref stop x)

private theorem linear_push (i : ℕ) {f : Config G (R.family.side (i+1) p) → ℂ}
    (paid : Integrable f (prior G (R.family.side (i+1) p))) :
    Integrable (transition (C:=R.family) d N p i f) (prior G (R.family.side i p)) := by
  unfold transition blast
  exact Integrable.smul _ (StepData.push_integrable (R.family.path.levels.transition_mass i p _) f paid)

/-- The literal signed transfer of a physical field loses no contact term.
Only the fine field's actual integrability is needed. -/
theorem successor (i : ℕ) (ref : R.family.ref d ≤ i) (stop : i<N) (x : R.family.label d)
    {f : Config G (R.family.side (i+1) p) → ℂ} (paid : Integrable f (prior G _)) :
    transition (C:=R.family) d N p i (f-calValues (C:=R.family) d N p (i+1) x) =
      transition (C:=R.family) d N p i f-calValues (C:=R.family) d N p i x := by
  have fine := column R d N p (i+1) (ref.trans (Nat.le_succ i)) stop x
  have add := transition_add d N p (i:=i) (paid.sub fine) fine
  rw [_root_.sub_add_cancel] at add
  exact (eq_sub_of_add_eq add.symm).trans (congrArg (fun q => transition (C:=R.family) d N p i f-q)
    (factory_eq d N p i R.makes ref stop x).symm)

private theorem cal_sub (i : ℕ) (ref : R.family.ref d ≤ i) (stop : i ≤ N) (a b : R.family.label d) :
    calValues (C:=R.family) d N p i (a-b) = calValues (C:=R.family) d N p i a-calValues (C:=R.family) d N p i b := by
  have e := cal_add d N p i R.makes ref stop (a-b) b
  have same : calValues (C:=R.family) d N p i a =
      calValues (C:=R.family) d N p i (a-b)+calValues (C:=R.family) d N p i b := by
    exact (congrArg (fun q : R.family.label d => calValues (C:=R.family) d N p i q)
      (show a = a-b+b by abel)).trans e
  exact eq_sub_of_add_eq same.symm

/-- Change the horizontal label at capture by exactly the label fixed at
the coarser physical reference. The same true zero-germ source, price,
and complete signed density remain at this actual cutoff and period. -/
theorem birth {b : ℕ} (ref : R.family.ref d ≤ b) (stop : b ≤ N)
    (x : R.family.label d) (err : Er R.family p) {q : store R.family d p b} {y : R.family.label d} {B : ℝ}
    (shot : Shot R.family d N p err b q y B) :
    Shot R.family d N p (subtract R d N p x err) b q (y-x) B := by
  refine ⟨shot.ready,shot.zero,?_⟩
  change err b-calValues (C:=R.family) d N p b x = value (C:=R.family) d N p b q+calValues (C:=R.family) d N p b (y-x)
  rw [shot.detailed,cal_sub R d N p b ref stop]
  abel

private theorem costs (u b : ℕ) (ref : R.family.ref d ≤ u) (stop : b ≤ N)
    (err f : Er R.family p) {D B : ℝ}
    (moves : ∀ i ≥ u, i<b → Foreground R.family d N p i (f i) D ∧
      err i = transition (C:=R.family) d N p i (err (i+1))+f i)
    (top : ∃ q y, Shot R.family d N p err b q y B) (j : ℕ) (jb : j ≤ b) :
    u ≤ j → Integrable (err j) (prior G (R.family.side j p)) := by
  induction jb using Nat.decreasingInduction with
  | self =>
    intro ub
    obtain ⟨q,y,paid⟩ := top
    rw [paid.detailed]
    exact (message d N p _ R.makes (ref.trans ub) stop paid.ready).add
      (column R d N p _ (ref.trans ub) stop y)
  | of_succ j jb next =>
    intro uj
    obtain ⟨⟨e,q,_,paid,_,shown,_⟩,move⟩ := moves j uj jb
    rw [move]
    apply (linear_push R d N p j (next (uj.trans (Nat.le_succ j)))).add
    rw [←shown]
    exact message d N p j R.makes (ref.trans uj) (jb.le.trans stop) paid

/-- The entire foreground/recurrence premise of the original zero-jet
crossing is valid for the newly signed field, with exactly the *original*
forcing and bound D at each step of the finite reference interval.
No integrability or centered evolution needs to be resupplied. -/
theorem propagation {u b : ℕ} (ref : R.family.ref d ≤ u) (stop : b ≤ N)
    (x : R.family.label d) (err f : Er R.family p) {D B : ℝ}
    (moves : ∀ i ≥ u, i<b → Foreground R.family d N p i (f i) D ∧
      err i = transition (C:=R.family) d N p i (err (i+1))+f i)
    (top : ∃ q y, Shot R.family d N p err b q y B) :
    ∀ i ≥ u, i<b → Foreground R.family d N p i (f i) D ∧
      (subtract R d N p x err) i =
        transition (C:=R.family) d N p i ((subtract R d N p x err) (i+1))+f i := by
  intro i ui ib
  obtain ⟨prepaid,move⟩ := moves i ui ib
  refine ⟨prepaid,?_⟩
  have incoming := costs R d N p u b ref stop err f moves top (i+1) ib (ui.trans (Nat.le_succ i))
  change err i-calValues (C:=R.family) d N p i x =
    transition (C:=R.family) d N p i (err (i+1)-calValues (C:=R.family) d N p (i+1) x)+f i
  rw [successor R d N p i (ref.trans ui) (ib.trans_le stop) x incoming,move]
  abel

end YM.Integration.WilsonCapturedFactoryCocycle
end
