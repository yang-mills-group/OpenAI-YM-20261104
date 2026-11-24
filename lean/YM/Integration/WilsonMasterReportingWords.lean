import YM.Integration.WilsonReportingLength
import YM.Integration.FilteredWilsonProduct
import YM.RG16.Unmasked.Purchased

/-! Coordinates of an independently prescribed Wilson field in the actual
finite reporting chart, including its coupling and lattice-spacing factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMasterReportingWords
open Function Lattice Wilson RG Cells OPE OPE.Orbits PhysMS Trace.Pilot
open Trace.Physical.GermGraph RG16 RG16.Literal FilteredIntrinsicGramReadout
open FilteredWilsonProduct EngineeringWeightedReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- Convert the prescribed terminal label using the inverse of the genuine
terminal identification, before applying the actual local coupling convention. -/
def coordinates (H : C.Makes) (N p d m : ℕ) (ho : Opened C d m p) (hm : m ≤ N)
    (y : C.label d) : C.label d :=
  dress C N p d H m ho hm ((C.factory d N p).terminal.symm y)

theorem reads (H : C.Makes) (N p d m : ℕ) (ho : Opened C d m p) (hm : m ≤ N)
    (y : C.label d) :
    master C N p d H m ho hm (coordinates H N p d m ho hm y) = y :=
  (dress_inverse C N p d H m ho hm _).trans ((C.factory d N p).terminal.apply_symm_apply _)

variable {I : Type} [Fintype I] {d : I → ℕ}

omit [Fintype I] in
theorem layout (m : ℕ) (B M η : ℝ) (x : I → Cover)
    (room : WithinRoom (WilsonReportingLength.radius C B m) M η (C.S.gridPoint m ∘ x) 0) :
    Tuple C M η B m ((Lambda C.path.levels m)^B) x := by
  refine ⟨le_rfl,Real.rpow_le_rpow_of_exponent_le (one_le_two.trans (lambda_up C m).le)
    (by linarith),fun i => ?_,fun i j hij => room.spaced i j hij⟩
  simpa only [Function.comp_apply,sub_zero,WilsonReportingLength.radius,
    WilsonReportingLength.unit,Lambda] using room.span i

theorem replica (H : C.Makes) (N p m : ℕ) (hm : m ≤ N)
    (op : ∀ i, Opened C (d i) m p) (x : I → Cover) (y : (i : I) → C.label (d i)) :
    Words C H d p N m (fun i => coordinates H N p _ m (op i) hm (y i)) x hm op =
      ∏ i,C.O N p (y i) (location C.S m N p (x i)) := by
  funext U
  simp only [Words,reads,snap,Cells.location,dif_pos hm,Finset.prod_apply]

/-- Expand the whole signed product in true numerical masters; the grades
are those of the original physical reader at the prescribed scale. -/
theorem field (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (N p m : ℕ) (hm : m ≤ N) (x : I → Cover)
    (op : ∀ (g : Grades d) i, Opened C (levels g i) m p) :
    FilteredWilsonProduct.field F R J v r m x (N,p) =
      ∑ g : Grades d, Words C F.room.cutoff (levels g) p N m
        (fun i => coordinates F.room.cutoff N p _ m (op g i) hm (component F R J v g r i))
        x hm (op g) := by
  rw [field_expansion]
  apply Finset.sum_congr rfl
  intro g _
  rw [replica]
  rfl

end YM.Integration.WilsonMasterReportingWords

