import YM.Integration.WilsonReportColumnCut
import YM.Integration.WilsonPhysicalMarkedDefectStoredInterior

/-! Measured finite windows in the physical g coordinates. Each field uses
the deposited original factory coefficient and its independently funded old
sections; the signed retained regular rows have a uniform absolute invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowSource
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Vitrines Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato
open WilsonPhysicalMarkedDefect.StoredInterior
open scoped Topology Classical BigOperators
variable {G : Gauge} (C : Family G) {d k N p : ℕ}

def retained (v : C.label d) (i : ℕ) (x : Site (C.side k p)) (U : Config G (C.side k p)) : ℂ :=
  let Q := parcel C d k N p v
  let A := C.path.rep N p k
  if height A Q i < (C.path.levels.budget k).B then
    alto C.path k d * Q.maskedTerm A i (pull 1 x U) else 0

def opened (v : C.label d) (x : Site (C.side k p)) (U : Config G (C.side k p)) : ℂ :=
  let Q := parcel C d k N p v
  alto C.path k d * (Q.x 0 + fitted C N p d k Q (pull 1 x U)) +
    ∑' i,retained C (N:=N) v i x U

def alarm (v : C.label d) (x : Site (C.side k p)) (U : Config G (C.side k p)) : ℂ :=
  alto C.path k d * failed C N p d k (parcel C d k N p v) (pull 1 x U)

/-- The actual registered near field, with its *full* individual signed terms,
their absolute summability before all backgrounds and all translations, and
the genuine unmodified section at the physical coupling with explicit alarm. -/
theorem actual (law : C.Makes) (grade : C.ref d≤k) (cut : k≤N) (v : C.label d) :
    let Q := parcel C d k N p v; let A := C.path.rep N p k; let D := C.labels.level d
    let z := (C.path.levels.params k).columns
    Q.Format 0 C.params A ∧
    Q.remBound 0 A (Real.sqrt (C.path.levels.clock.forcedAllowance k)) (z*D.coeffSize (D.core Q.x)) ∧
    (∃ a : ℕ→ℝ, (∀ i,0≤a i) ∧ Summable a ∧ (∑' i,a i)≤z*Spindle.paid C d k N p v ∧
      ∀ i (x : Site (C.side k p)) (U : Config G (C.side k p)), ‖retained C (k:=k) (N:=N) (p:=p) v i x U‖ ≤ a i) ∧
    ∀ x U, bead C d k N p (C.path.levels.budget k).B v x U =
      opened C (N:=N) v x U + alarm C (N:=N) v x U := by
  let Q := parcel C d k N p v
  let A := C.path.rep N p k
  let D := C.labels.level d
  let z := (C.path.levels.params k).columns
  let α := alto C.path k d
  let B := (C.path.levels.budget k).B
  have invest := law.calibrated d N p (grade.trans cut)
  have form : Q.Format 0 C.params A := invest.format k grade cut _
  have cap : Q.remBound 0 A (Real.sqrt (C.path.levels.clock.forcedAllowance k)) (z*D.coeffSize (D.core Q.x)) :=
    invest.cap k grade cut _
  have columns0 : 0≤z := zero_le_one.trans (C.path.levels.params k).columns_ge
  dsimp only
  refine ⟨form,cap,?_,?_⟩
  · obtain ⟨a,b,_,hb,total,_,⟨e,book,sold⟩,_⟩ := cap
    let fee (i : ℕ) := A.p.mass (Q.support i) (e i)
    have prices (i : ℕ) (U : Config G (C.side k p)) : ‖Q.maskedTerm A i U‖ ≤ fee i := by
      apply le_trans (b:=e i) _ (A.p.loMass _ _ (sold i).1)
      by_cases live : Healthy A.p.threshold (Q.support i) U
      · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ live]
        exact (sold i).2 U live [] (Nat.zero_le _) (by simp)
      · rw [Coefficient.maskedTerm,masked_ne _ _ _ _ live,norm_zero]
        exact (sold i).1
    have finite : Summable fee := book.2.1
    have limited : (∑' i,fee i)≤z*D.coeffSize (D.core Q.x) := book.2.2.trans (by linarith only [total,hb])
    refine ⟨fun i=>‖α‖*fee i,fun i=>mul_nonneg (norm_nonneg _) (book.1 i),finite.mul_left _,?_,?_⟩
    · rw [tsum_mul_left]
      calc
        _ ≤ ‖α‖*(z*D.coeffSize (D.core Q.x)) := mul_le_mul_of_nonneg_left limited (norm_nonneg _)
        _ ≤ z*(‖α‖*D.coeffSize Q.x) := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (core_le C d _) (norm_nonneg _)) columns0
        _ = _ := congrArg (z*·) (mintedLabel (k:=k) (N:=N) (p:=p) v).symm
    intro i x U
    unfold retained
    dsimp only
    split
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (prices i _) (norm_nonneg _)
    · rw [norm_zero]
      exact mul_nonneg (norm_nonneg _) (book.1 i)
  intro x U
  let V := pull 1 x U
  have paid := near_form (C.localSection d) cap B V
  have primaryMask : masked A.p.threshold ((C.localSection d).footprint 0)
      ((C.localSection d).places (D.scaled A.p.threshold⁻¹ (D.core Q.x)) 0) V =
      fitted C N p d k Q V + failed C N p d k Q V := by
    by_cases live : Healthy A.p.threshold ((C.localSection d).footprint 0) V
    · rw [masked_eq _ _ _ _ live,failed,if_pos live,add_zero]
      exact primary C N p d k law cut Q V
    · rw [masked_ne _ _ _ _ live,failed,if_neg live,add_neg_cancel]
  let row (i : ℕ) := if height A Q i<B then Q.maskedTerm A i V else 0
  have scaled (i : ℕ) : retained C (N:=N) v i x U = α*row i := by
    unfold retained; dsimp only [row,α,Q,A,B,V]
    split <;> simp
  change α*enamel (C.localSection d) A Q B V=α*(Q.x 0+fitted C N p d k Q V)+
    (∑' i,retained C (N:=N) v i x U)+α*failed C N p d k Q V
  rw [paid,primaryMask]
  simp_rw [scaled]
  rw [tsum_mul_left]
  change α*(Q.x 0+(fitted C N p d k Q V+failed C N p d k Q V)+(∑'i,row i))=_
  ring

end YM.Integration.WilsonReportWindowSource
end

