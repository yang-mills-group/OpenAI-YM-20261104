import YangMills.WilsonProof.NativeSupport.JointPhysicalDock
import YangMills.WilsonProof.NativeSupport.JointMountedPush
import YangMills.WilsonProof.NativeSupport.JointPhysicalVisit

/-! Admission and exact reconstruction for the entire native same-key heap
used by the selected physical marked push. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Filter Lattice Wilson RG Pressure Tree MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil
open Progress.DirectedRecipe Planned.GuardedAtom
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {I V : Type} [Fintype I] [DecidableEq V] {B:Census V} {G:Gauge} {f c:Side} {R:Rep G f}
variable (q:I→Hat B R)

theorem heap_reserved (blank : ∀ i (Z:Rep G f),HasSlots Z.p Z.activities→(q i).M.turn.blank Z)
    (j:Mound q) (Z:Rep G f) (slots:HasSlots Z.p Z.activities) : (heap q j).M.turn.blank Z := by
  rcases j with i|j
  · exact blank i Z slots
  obtain ⟨i,hi⟩:=j.2.val.property.1
  have same : WKey (q i)=Wing.logKey j.1.val := (mem_filter.mp (j.2.val.property.2.1 hi)).2
  change (Wing.logKey j.1.val).blank Z
  rw [←same]
  exact blank i Z slots

variable {K:Support f → Config G f→Poly B} {F:Box f → Config G f→Poly B}
theorem heap_density [Fintype V] {σ C g δ v:ℝ} (law:R.Lawful σ C g δ v) (w:V→ℝ) (hw:∀ i,0<w i)
    (S:StepData c f) (regular:∀ U,∑ j,odour (q j) U=∑ i,K i U)
    (dirty:∀ i U,∑ j,fragrance (q j) U i=F i U) :
    Expense (heap q) w S=play R B (exclaim R.activities B+F) (fun U=>∑ i,K i U) := by
  funext U
  rw [Expense,passIn (heap q) S law hw U,Menu.golden,banded,perfumes,regular]
  simp_rw [patron,dirty]
  rfl

theorem anchored_heap {o:V→Site f} {d a:ℝ} (S:StepData c f) (J:V→Finset (Bond c))
    (w:V→ℝ) (offer:Offer o (heap q) w R.p.B d a)
    (anchors:∀ i j,j∈J i → o i=S.ratio.embed j.1) (i:Mound q) (j:Bond c)
    (hit:j∈JointLeaves.bonds J (heap q i).s.val) : S.ratio.embed j.1∈(heap q i).M.crest := by
  obtain ⟨v,hv,hj⟩:=mem_biUnion.mp hit
  rw [←anchors v j hj]
  exact offer.sites i (mem_image_of_mem o hv)

omit [Fintype I] [DecidableEq V] in
theorem old_heap_tests {Q : Type} (J:V→Finset Q) (fresh:Finset V) (empty:∀ i,i∉fresh → J i=∅)
    (s:Finset V) (old:Disjoint s fresh) : (s.biUnion J)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a mem
  obtain ⟨i,hi,hq⟩:=mem_biUnion.mp mem
  rw [empty i (disjoint_left.mp old hi)] at hq
  exact notMem_empty a hq

end YM.Integration.InletSusceptibility.JointShadow

namespace YM.Integration.InletSusceptibility.BoardAdmission
open RG Wilson Lattice PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Muse PhysicalNext.Repeat.Muse.Veil
open PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams FullVolume.Ray FullVolume.Urns
open Extra.Iteration Progress.DirectedRecipe
open PhysicalNext.Repeat.Roof RG.Shoot
variable {G : Gauge} {R : Run G} {N m n : ℕ} {T : Team (stageP R.alloy.B.a (m+1) n)}

theorem original_forced_intake (y : Booker R.alloy N m n T) :
    ∃ a:ℝ,y.val.val.val.activities.Valid y.val.val.val.p a (R.alloy.B.a.clock.forcedAllowance (m+1)) :=
  ⟨_, y.val.val.property.1.valid.labels⟩

end YM.Integration.InletSusceptibility.BoardAdmission
