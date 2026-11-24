import YangMills.WilsonProof.NativeSupport.JointRepaint
import YangMills.WilsonProof.NativeSupport.JointMountFlags

/-! The change of ownership preserves the native field, flag, and
support predicates. Forgetting ownership commutes with the complete
unnormalized regular/forced representation, not only its linear part. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Finset Function Lattice RG Wilson Marker Packet MergeProof MergeProof.Accent MeasureTheory
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : Gauge} {n : Side} {o : V → Site n} {X : Support n} {t : ℝ}

theorem project_quiet (P : Poly (YM.Stock.census (Ink V))) :
    (project P).part (tag ∅)=P.part (tag ∅) := by
  rw [projected_part,sum_eq_single ∅]
  · intro s hs ne
    exact False.elim (ne (Finset.image_eq_empty.mp (mem_filter.mp hs).2.2))
  · intro no
    exact False.elim (no (mem_filter.mpr ⟨mem_univ _,by simp [faithful]⟩))

theorem repaint_quiet (P : Poly (YM.Stock.census V)) :
    (repaint P).part (tag ∅)=P.part (tag ∅) := by simp [repaint_part,wear]

theorem repaint_nil : repaint (0 : Poly (YM.Stock.census V))=0 := by
  ext s
  change (repaint (0 : Poly (YM.Stock.census V))).part (tag s.val)=0
  rw [repaint_part]
  split <;> rfl

theorem born_project (F : Config G n → Poly (YM.Stock.census (Ink V)))
    (h : Borne (o ∘ Prod.fst) X F t) : Borne o X (fun Z=>project (F Z)) t := by
  refine ⟨fun U Z near flags=>congrArg project (h.home U Z near flags),
    fun k U=>congrArg project (h.turns k U),?_,?_⟩
  · intro p
    change Measurable fun Z=>(project (F Z)).part (tag p.val)
    simp_rw [projected_part]
    exact Finset.measurable_fun_sum _ fun S _=>h.me (tag S)
  · intro Z p outside
    change (project (F Z)).part (tag p.val)=0
    rw [projected_part]
    refine sum_eq_zero fun S includes=>h.scope Z (tag S) ?_
    intro inner
    apply outside
    intro v hv
    obtain ⟨i,hi,rfl⟩:=mem_image.mp (((mem_filter.mp includes).2.2).symm ▸ hv)
    exact inner hi

theorem born_repaint (F : Config G n → Poly (YM.Stock.census V)) (h : Borne o X F t) :
    Borne (o ∘ Prod.fst) X (fun Z=>repaint (F Z)) t := by
  refine ⟨fun U Z near flags=>congrArg repaint (h.home U Z near flags),
    fun k U=>congrArg repaint (h.turns k U),?_,?_⟩
  · intro p
    change Measurable fun Z=>(repaint (F Z)).part (tag p.val)
    simp_rw [repaint_part]
    by_cases seen : p.val=wear (p.val.image Prod.fst)
    · simpa only [if_pos seen] using h.me (tag (p.val.image Prod.fst))
    · simpa only [if_neg seen] using (show Measurable (fun _:Config G n=>(0:ℂ)) from measurable_const)
  · intro Z p outside
    change (repaint (F Z)).part (tag p.val)=0
    rw [repaint_part]; split
    · apply h.scope Z
      intro some
      exact outside (fun i hi=>some (mem_image_of_mem _ hi))
    · rfl

theorem project_pass (P : Poly (YM.Stock.census (Ink V))) (quiet : P.part (tag ∅)=0) :
    project (Poly.pass P)=Poly.pass (project P) := by
  have q : (project P).part (YM.Stock.census V).quiet=0 := (project_quiet P).trans quiet
  rw [Poly.pass,map_sum,Poly.pass]
  have lin (x:ℂ) (a:Poly (YM.Stock.census (Ink V))) : project (x • a)=x • project a :=
    MarkerSubstitution.on_smul plain x a
  simp_rw [lin,map_pow]
  apply Eq.symm
  apply Finset.sum_subset
  · apply range_mono
    simp [Ink]
    omega
  · intro i _ missing
    have high : Fintype.card V < i := by simp only [mem_range] at missing; omega
    rw [Poly.stops _ q i high,smul_zero]

theorem project_play (R : Rep G n)
    (K : Box n → Config G n → Poly (YM.Stock.census (Ink V)))
    (H : Config G n → Poly (YM.Stock.census (Ink V))) (Z:Config G n)
    (quiet : (H Z).part (tag ∅)=0) :
    project (play R (YM.Stock.census (Ink V)) K H Z)=
      play R (YM.Stock.census V) (fun i U=>project (K i U)) (fun U=>project (H U)) Z := by
  unfold play
  rw [show ∀ (c:ℂ) (P : Poly (YM.Stock.census (Ink V))), project (c • P)=c • project P from
    fun c P=>MarkerSubstitution.on_smul plain c P,map_mul,project_pass _ quiet]
  simp only [field,grid,map_sum,apply_ite project,map_zero,map_prod]

end YM.Integration.InletSusceptibility.Painted
