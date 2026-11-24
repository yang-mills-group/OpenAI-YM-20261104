import YM.Integration.WilsonCenteredActualHardSum
import YM.Integration.WilsonCenteredCaptureOwnerTariff

/-! A failed common halo with no previously marked hard owner. Absorb
the original quiet owners that meet the actual query. At least one is
present whenever its signed correction is nonzero. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredFailedHalo
open Function Finset Lattice RG Wilson Marker Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCapturePush WilsonCenteredCaptureCensus WilsonCenteredCaptureSlots
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} {P : Rep G n}
    (T : ι→Support n) (K : Guard.Keeper P.p P.activities) (serial : ι × Finset ℕ ↪ ℕ)

abbrev Quiet (_ : ι) : Finset ℕ := ∅
def bag (q : Key P T Quiet) : (i : ι) × Pack P.activities (T i) :=
  ⟨q.val.1,⟨q.val.2,q.property.live,q.property.apart,fun j hj=>(q.property.hits j hj).resolve_left (notMem_empty _)⟩⟩

theorem noDouble : Injective (bag (P:=P) T) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun s : (i : ι) × Pack P.activities (T i)=>(s.1,s.2.val)) h

theorem cost (f : ι → Config G n→ℂ) (e : ι→ℝ) {v b : ℝ}
    (quiet : P.activities.KBound P.p v) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (pos : ∀ i,0≤e i) (income : SumBudget (fun i=>reservedMass P.p (T i) (e i)) b)
    (cap : ∀ i U, ‖f i U‖ ≤ e i) :
    ForceCost P.p P.activities (entered P K T Quiet serial f) ((hitWidth P.p*v)*b) := by
  obtain ⟨k,kb,_,paid⟩ := WilsonCenteredCaptureOwnerTariff.collection T e quiet hv room pos income
  let W (s : (i : ι) × Pack P.activities (T i)) := e s.1*∏ j ∈ s.2.val, k j
  let mass (s : (i : ι) × Pack P.activities (T i)) :=
    P.p.mass (T s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities)) (W s)
  let code := slot P K T Quiet serial
  let price := Function.extend code (W ∘ bag (P:=P) T) 0
  have note (q : Key P T Quiet) : price (code q) = W (bag T q) := code.injective.extend_apply ..
  have idle (i : ℕ) (hz : ¬∃ q, code q=i) : price i=0 := Function.extend_apply' _ _ _ hz
  have small : SumBudget (mass ∘ bag (P:=P) T) ((hitWidth P.p*v)*b) :=
    ⟨fun _=>paid.1 _,paid.2.1.comp_injective (noDouble T),
      (tsum_comp_le_tsum_of_inj paid.2.1 paid.1 (noDouble T)).trans paid.2.2⟩
  refine ⟨price,sumBudget_pass code _ ?_ ?_,?_⟩
  · have eq (q : Key P T Quiet) : P.p.mass (Push.Local.patch P.activities (code q)) (price (code q)) = mass (bag T q) := by
      rw [note]
      exact congrArg (fun Z=>P.p.mass Z (W (bag T q))) (support P K T Quiet serial q)
    simp_rw [eq]
    exact small
  · intro j hj
    rw [idle j hj]
    exact mul_zero _
  intro j
  by_cases used : ∃ q, code q=j
  · obtain ⟨q,rfl⟩ := used
    rw [note]
    have positive : 0 ≤ W (bag T q) := mul_nonneg (pos _) (prod_nonneg fun j _=>(kb j).1)
    refine ⟨positive,?_⟩
    intro U
    change ‖entered P K T Quiet serial f (slot P K T Quiet serial q) U‖ ≤ _
    rw [registered]
    unfold payload
    split
    · simp only [Quiet,sdiff_empty,norm_mul,norm_prod]
      apply mul_le_mul (cap _ _) _ (prod_nonneg fun _ _=>norm_nonneg _) (pos _)
      exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>by simpa using (kb j).2 U)
    · simpa using positive
  · rw [idle j used,outside P K T Quiet serial f j used]
    exact ⟨le_rfl,fun _=>norm_zero.le⟩

theorem present {f : ι → Config G n→ℂ} (attached : ∀ i, Attaches P.p.threshold (T i) (f i))
    (U : Config G n) (i : ι) (F : Finset ℕ) (old : P.activities.admissible P.p U F)
    (nz : f i U ≠ 0) : (taken P (T i) ∅ F).Nonempty := by
  by_contra h
  have blank := not_nonempty_iff_eq_empty.mp h
  have tags := exact_flags P (T i) ∅ F U old
  rw [blank] at tags
  have cool : Healthy P.p.threshold (T i) U := by
    apply disjoint_iff_inter_eq_empty.mpr
    simpa [ground,flagsOf] using tags
  exact nz ((attached i).healthy_zero U cool)

def originalIndex (U : Config G n) (s : Born P T Quiet U) := (s.1,s.2.val)
theorem faithful (U : Config G n) : Injective (originalIndex (P:=P) T U) := by
  rintro ⟨i,⟨F,t⟩⟩ ⟨j,⟨E,u⟩⟩ h
  change (i,F)=(j,E) at h
  cases h
  rfl

theorem actual (f : ι → Config G n→ℂ) (attached : ∀ i,Attaches P.p.threshold (T i) (f i))
    {v b : ℝ} (paid : ForceCost P.p P.activities (entered P K T Quiet serial f) b)
    (quiet : P.activities.KBound P.p v) (U : Config G n) :
    (∑' F,gasMark P.p P.activities U F (entered P K T Quiet serial f)) =
      (∑' i,f i U) * (P.activities.gas P.p U : ℂ) := by
  let word (q : ι × Finset ℕ) := f q.1 U * (P.activities.gasOccurrence P.p q.2 U : ℂ)
  have journal := WilsonCenteredActualHardSum.retained K T Quiet serial f paid quiet U
  have zeroOut (s : ι × Finset ℕ) (spare : s ∉ Set.range (originalIndex (P:=P) T U)) : word s=0 := by
    by_cases old : P.activities.admissible P.p U s.2
    · by_cases stamped : f s.1 U=0
      · simp [word,stamped]
      exact (spare ⟨⟨s.1,⟨s.2,old,empty_subset _,present T attached U _ _ old stamped⟩⟩,rfl⟩).elim
    simp [word,Activities.gasOccurrence,old]
  have full : HasSum word (∑' F,gasMark P.p P.activities U F (entered P K T Quiet serial f)) := by
    apply ((faithful T U).hasSum_iff zeroOut).1
    apply journal.congr_fun
    intro z
    simp [word,originalIndex,Activities.gasOccurrence,Quiet,z.2.property.1,Complex.ofReal_prod]
  rw [←full.tsum_eq,full.summable.tsum_prod]
  have all (i : ι) : (∑' F,word (i,F))=f i U*(P.activities.gas P.p U:ℂ) := by
    simp [word,tsum_mul_left,Activities.gas,Complex.ofReal_tsum]
  simp_rw [all,tsum_mul_right]

end YM.Integration.WilsonCenteredFailedHalo
