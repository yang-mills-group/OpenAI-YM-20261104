import YM.Integration.WilsonOriginalNullDensity

/-! Assemble the regular rows and the fired hard family into a native guarded
deck. Scaling a hard row keeps its original addresses and its quiet partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullCarrier
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Ac MeasureTheory
open Extra.Histories Push.Local Overlay Fusion.Attached Extra.Multi Planned.GuardedAtom
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {C : Census Unit} {d : ℕ} {F : Frame G d} {P : Rep G n}
    {o : Unit → Site n} (H : Hard Unit P.p P.activities.forced P.activities.K o C)
    (f : ℕ → Config G n → ℂ) (z : ℂ)

def raw : Raw F n := ⟨0,f,z • (WilsonMeasuredSingletonForce.row (F:=F) H () ()).forced⟩

theorem original (A : Hol G) (X : ℕ → Support n) (κ a b : ℝ)
    (root : ∀ i, o () ∈ X i) (shape : ∀ i, P.p.Regular (X i) (f i))
    (bulk : ∃ e : ℕ → ℝ, (∀ j, P.p.supBounds (o ()) (X j) (f j) (e j)) ∧
      SumBudget (fun j => reservedMass P.p (X j) (e j)) a)
    (paid : (WilsonMeasuredSingletonForce.row (F:=F) H () ()).remBound (o ()) P κ b) :
    (raw (F:=F) H f z).Format (o ()) X P ∧ Deck (raw (F:=F) H f z) (o ()) X P κ a (‖z‖*b) := by
  let M := WilsonMeasuredSingletonForce.row (F:=F) H () ()
  have fmt := WilsonMeasuredSingletonForce.format (F:=F) H () () A
  have before : ForceFormat P.p P.activities (o ()) M.forced :=
    ⟨fmt.forcing,fmt.carried,fmt.invariant,fmt.supported,fmt.borel⟩
  obtain ⟨s,t,ns,_,st,hκ,_,e,cap,fee⟩ := paid
  have budget : ForceCost P.p P.activities M.forced (κ*b) := by
    refine ⟨e,?_,fee⟩
    refine ⟨cap.1,cap.2.1,cap.2.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left ns).trans st) hκ.le
  obtain ⟨format,restored⟩ := WilsonCenteredSingletonMass.scaled z M.forced before budget
  exact ⟨⟨root,shape,format⟩,bulk,by simpa [raw,M,mul_left_comm] using restored⟩

theorem read (S : SectionData F) (X : ℕ → Support n) (U : Config G n) :
    (raw (F:=F) H f z).eval (o ()) X S P U =
      (P.eval U : ℂ) * (∑' j, masked P.p.threshold (X j) (f j) U) +
      z * (WilsonMeasuredSingletonForce.row H () ()).density (o ()) S P U := by
  let M := WilsonMeasuredSingletonForce.row (F:=F) H () ()
  have head : M.exponentialEntry (o ()) S P U=0 := by
    simp [M,WilsonMeasuredSingletonForce.row,Extra.Histories.primary,Coefficient.exponentialEntry,
      Coefficient.maskedTerm,masked,SectionData.places,SectionData.evaluate]
  have atom (s : Finset ℕ) :
      gasMark P.p P.activities U s ((raw (F:=F) H f z).forced) = z * M.marked P s U := by
    change gasMark P.p P.activities U s (z • M.forced) = _
    rw [map_smul, smul_eq_mul]
    exact congrArg (z * ·) (gasMark_eq P.p P.activities U s M.forced)
  change (P.eval U : ℂ) * (Push.Local.primary S (o ()) P.p.threshold 0 U + _) +
    (Real.exp (P.exponent U):ℂ) * ∑' s, gasMark P.p P.activities U s ((raw (F:=F) H f z).forced) = _ + z * M.density (o ()) S P U
  simp_rw [atom]
  rw [tsum_mul_left, Coefficient.density,head]
  simp only [raw,map_zero,Pi.zero_apply,zero_add,mul_zero]
  ring

end YM.Integration.WilsonOriginalNullCarrier
