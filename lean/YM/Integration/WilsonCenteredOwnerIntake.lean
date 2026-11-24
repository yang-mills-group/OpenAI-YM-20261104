import YM.Integration.WilsonCenteredKeptOwners

/-! A true hard operand is read on its complete physical support. The
additional quiet pack is charged on the submitted query. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOwnerIntake
open Finset Function Lattice RG Wilson Push.Local Planned.GuardedAtom MeasureTheory
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredKeptOwners
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} (P : Rep G n) (T : ι→Support n) (I : ι→Finset ℕ)
variable (K : Guard.Keeper P.p P.activities) (serial : ι×Finset ℕ ↪ ℕ)

lemma receives (q : Key P T I) : ground P (T q.val.1) (I q.val.1) ⊆ ground P (T q.val.1) q.val.2 := by
  intro y hy
  rcases mem_union.mp hy with okay|active
  · exact mem_union_left _ okay
  obtain ⟨j,hj,atJ⟩:=mem_biUnion.mp active
  exact mem_union_right _ (mem_biUnion.mpr ⟨j,q.property.kept hj,atJ⟩)

theorem formed (f : ι→ Config G n→ℂ) (o : Site n)
    (law : P.activities.ForcedFamily P.p) (anchor : ∀ z,o∈T z)
    (symm : ∀ z,GaugeInvariant (f z)) (borel : ∀ z,Measurable (f z))
    (locality : ∀ z,UsesFinal P.p.threshold (ground P (T z) (I z)) (f z)) :
    ForceFormat P.p P.activities o (entered P K T I serial f) := by
  refine ⟨fun j U neq=>?_,fun j neq=>?_,fun j=>?_,fun j=>?_,fun j=>?_⟩
  all_goals by_cases used : ∃ q, slot P K T I serial q = j
  all_goals first | obtain ⟨q,rfl⟩ := used | simp only [outside P K T I serial f j used] at *
  · rw [registered,payload] at neq
    split at neq
    · assumption
    exact (neq rfl).elim
  · exact (neq rfl).elim
  · rw [show Push.Local.patch P.activities (slot P K T I serial q) = ground P (T q.val.1) q.val.2 from support ..]
    exact mem_union_left _ (anchor q.val.1)
  · exact (neq rfl).elim
  · intro gauge U
    rw [registered,payload,payload]
    simp only [Work.H03.eligible_gauge _ _ _ _ (law.symtest _ gauge U),(symm q.val.1) gauge U,fun j=>law.sym j gauge U]
  · intro _ _
    rfl
  · rw [registered]
    intro U V huv hflags
    unfold payload
    rw [Work.H03.eligible_reads _ _ (law.reads_test _) U V huv hflags]
    rw [show Push.Local.patch P.activities (slot P K T I serial q) = ground P (T q.val.1) q.val.2 from support ..] at huv hflags
    split
    · rw [Work.H03.reads_larger (receives P T I q) (locality q.val.1) U V huv hflags]
      congr 1
      exact Finset.prod_congr rfl (fun j hj => congrArg Complex.ofReal (Work.H03.reads_larger
        ((Finset.subset_biUnion_of_mem _ (mem_sdiff.mp hj).1).trans Finset.subset_union_right)
        (law.reads j) U V huv hflags))
    rfl
  · intro _ _ _ _
    rfl
  · rw [registered]
    unfold payload
    exact Measurable.ite (Work.H03.eligible_measurable _ _ (law.meas_test _)) ((borel _).mul
      (Finset.measurable_fun_prod _ fun j _ => Complex.continuous_ofReal.measurable.comp (law.meas j))) measurable_const
  · exact measurable_const


theorem cost (f : ι→ Config G n→ℂ) (e : ι→ℝ) {v b : ℝ}
    (quiet : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1) (pos : ∀ i,0≤e i)
    (income : SumBudget (fun i=>reservedMass P.p (T i) (salary P I e i)) b)
    (home : ∀ z,e z≠0→∀ j∈I z,∃ u∈T z,u∈Push.Local.patch P.activities j)
    (cap : ∀ i U,‖f i U‖≤e i) :
    ForceCost P.p P.activities (entered P K T I serial f) (b+(hitWidth P.p*v)*b) := by
  have green i : 0 ≤ salary P I e i:=mul_nonneg (Real.exp_pos _).le (pos i)
  obtain ⟨k,kb,bare,paid⟩:=WilsonCenteredCaptureOwnerTariff.collection T (salary P I e) quiet hv room green income
  have total:=roster P T I e k pos (fun j=>(kb j).1) home bare paid
  let code:=slot P K T I serial
  let price:=Function.extend code (fee P T I e k) 0
  have atCode (q : Key P T I) : price (code q)=fee P T I e k q:=code.injective.extend_apply ..
  have idle (j : ℕ) (hz : ¬∃ q,code q=j) : price j=0:=Function.extend_apply' _ _ _ hz
  refine ⟨price,sumBudget_pass code _ ?_ ?_,?_⟩
  · have stage (q : Key P T I) : P.p.mass (Push.Local.patch P.activities (code q)) (price (code q)) =
        P.p.mass (ground P (T q.val.1) q.val.2) (fee P T I e k q) := by
      rw [atCode];exact congrArg (fun X=>P.p.mass X (fee P T I e k q)) (support P K T I serial q)
    simpa only [stage] using total
  · intro j hj;rw [idle j hj];exact mul_zero _
  intro j
  by_cases used : ∃ q,code q=j
  · obtain ⟨q,rfl⟩:=used
    rw [atCode]
    have nonneg : 0≤fee P T I e k q:=mul_nonneg (pos _) (prod_nonneg fun j _=>(kb j).1)
    refine ⟨nonneg,fun U=>?_⟩
    change ‖entered P K T I serial f (slot P K T I serial q) U‖≤_
    rw [registered]
    unfold payload
    split
    · simp only [norm_mul,norm_prod]
      apply mul_le_mul (cap _ _) _ (prod_nonneg fun _ _=>norm_nonneg _) (pos _)
      exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>by simpa using (kb j).2 U)
    simpa using nonneg
  rw [idle j used,outside P K T I serial f j used]
  simp

end YM.Integration.WilsonCenteredOwnerIntake
