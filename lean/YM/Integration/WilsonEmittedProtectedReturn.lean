import YM.Integration.WilsonEmittedHealthyField
import YM.Integration.WilsonCenteredMountedCapture
import YM.Integration.WilsonCenteredLampCapture

/-! The true old hard inventory pays the failed hull with its all-field
cap. The regular bill and the measured primary use the smaller signed
healthy bound, including when the failed-hull cap is much larger. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedProtectedReturn
open Function Finset Lattice RG Wilson Source Labels Push.Local Planned.GuardedAtom
open Push.AbsoluteSums WilsonCenteredCaptureSlots WilsonCenteredFailedHalo WilsonCenteredMountedCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} [Countable ι] {d : ℕ} {F : Frame G d}
  (P : Rep G n) (y : Site n) (T : ι → Support n) (f : ι → Config G n → ℂ)

omit [Countable ι] in
private theorem cheap (i : ι) (e : ℝ) (he : 0≤e) : e ≤ reservedMass P.p (T i) e := by
  apply le_mul_of_one_le_left he
  apply Real.one_le_exp
  exact mul_nonneg (by linarith [P.p.exponent_pos]) (Nat.cast_nonneg _)

omit [Countable ι] in
theorem unscreened (i : ι) (good : P.p.Regular (T i) (f i)) :
    Attaches P.p.threshold (T i) (f i-masked P.p.threshold (T i) (f i)) := by
  refine ⟨fun U V diff same => congrArg₂ Sub.sub (good.sites U V diff)
    (uses_mask _ good.sites U V diff same),fun t U => congrArg₂ Sub.sub (good.symmetry t U)
    (invariant_mask good.symmetry _ _ t U),good.borel.sub (masked_measurable _ _ _ good.borel),
    fun U hu=>?_⟩
  simp [masked_eq _ _ _ _ hu]

theorem funded (K : Guard.Keeper P.p P.activities) (S : SectionData F) (Y : Hol G)
    {σ C Λ δ u κ w a b : ℝ} (law : P.Lawful σ C Λ δ u) (div : 0<κ)
    (positive : 0≤u) (spare : hitWidth P.p*u≤1) (read : Readable Y S P.p n w)
    (roots : ∀ i, y∈T i) (regular : ∀ i,P.p.Regular (T i) (f i))
    (e E : ι→ℝ) (soft : SumBudget (fun i=>reservedMass P.p (T i) (e i)) a)
    (hard : SumBudget (fun i=>reservedMass P.p (T i) (E i)) b)
    (tested : ∀ i,P.p.supBounds y (T i) (f i) (e i)) (crude : ∀ i U, ‖f i U‖≤E i) :
    let bill := factor Y S P.p.supportExponent w * a
    let toll := hitWidth P.p*u/κ
    ∃ Q : Coefficient F n, Q.Format y Y P ∧
      Q.remBound y P κ (bill+(toll*b+toll*bill)) ∧ F.coeffSize Q.x≤bill ∧
      ∀ U,Q.density y S P U=(P.eval U:ℂ)*(∑' i,f i U) := by
  intro bill toll
  let book := WilsonCenteredLampCapture.docket ι
  let serial := WilsonCenteredLampCapture.docket (ι × Finset ℕ)
  let h := fun i => f i-masked P.p.threshold (T i) (f i)
  let M := raw T book K serial (0:F.Coeff) f h 0
  let A := halls y T book
  let rooms := K.supply (fun i=>joint S y (A i))
  have blank : ForceFormat P.p P.activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have no : ForceCost P.p P.activities (0 : ℕ → Config G n → ℂ) (κ*0) := by
    rw [mul_zero]
    exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  have att i : Attaches P.p.threshold (T i) (h i) := unscreened P T f i (regular i)
  have ok := formed y T book K serial (0:F.Coeff) f h 0 roots regular att blank law.labels.forced
  have l := deck y T book K serial (0:F.Coeff) f 0 0 e soft tested positive spare law.labels.boundK
    (fun i _=>by simpa using (tested i).1) no div
  have supE i : 0 ≤ E i := (norm_nonneg _).trans (crude i 1)
  have large (i : ι) U : ‖h i U‖≤E i := by
    by_cases ce : Healthy P.p.threshold (T i) U
    · simpa [h,masked_eq _ _ _ _ ce] using supE i
    · simpa [h,masked_ne _ _ _ _ ce] using crude i U
  have fee := WilsonCenteredFailedHalo.cost T K serial h E law.labels.boundK positive spare supE hard large
  have entry : Deck M y A P κ a (toll*b) := by
    refine ⟨l.bulk,?_⟩
    change ForceCost P.p P.activities (0+entered P K T Quiet serial h) (κ*(toll*b))
    rw [zero_add,show κ*(toll*b)=(hitWidth P.p*u)*b by dsimp [toll];field_simp]
    exact fee
  have fares := entry.tare div positive spare read ok
  refine ⟨Guard.mint rooms M Y,Guard.usage rooms ok law read,
    (Guard.tab_mint rooms ok law div read fares).bound le_rfl,?_,?_⟩
  · have hp:=Guard.size_mint rooms ok read fares (0:F.Coeff)
    simpa [M,raw,Frame.coeffSize] using hp
  intro U
  have range (i : ι) : ‖masked P.p.threshold (T i) (f i) U‖≤e i := by
    by_cases ce : Healthy P.p.threshold (T i) U
    · simpa [masked_eq _ _ _ _ ce,leftDerivs] using (tested i).2 U ce [] (Nat.zero_le _) (by simp)
    · simpa [masked_ne _ _ _ _ ce] using (tested i).1
  have hm := Summable.of_norm_bounded soft.2.1 (fun i=>(range i).trans (cheap P T i _ (tested i).1))
  have he := Summable.of_norm_bounded hard.2.1 (fun i=>(large i U).trans (cheap P T i _ (supE i)))
  rw [Guard.value_mint rooms ok law div read fares,value y T book K serial (0:F.Coeff) f h 0 S U att
    law.labels.boundK no fee hm he]
  simp [h]

end YM.Integration.WilsonEmittedProtectedReturn
