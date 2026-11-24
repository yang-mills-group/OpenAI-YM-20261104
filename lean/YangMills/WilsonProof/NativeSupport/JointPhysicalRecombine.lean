import YangMills.WilsonProof.NativeSupport.JointPhysicalMount
import YangMills.WilsonProof.NativeSupport.JointSelectedComponents

/-! Erase temporary ownership on the very same dated polynomial after
measuring bonds. This recovers the old physical density multiplied by
all of the physical primitive factors. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset RG Lattice Wilson Marker MergeProof MergeProof.Accent MergeProof.Menu Extra.Trajectories Packet Painted RGGapR2
open scoped Classical BigOperators
variable {V J:Type} [Fintype V] [DecidableEq V] [Fintype J]
local notation "B" => Stock.census V
local notation "C" => Stock.census (Ink V)

omit [Fintype J] in
theorem project_diagonal (a:V → ℂ) (P:Marker.Poly (Stock.census (Ink V))) :
    Painted.project (diagonal (a ∘ Prod.fst) P)=diagonal a (Painted.project P) := by
  ext q
  change (Painted.project _).part (tag q.val)=(diagonal a (Painted.project P)).part (tag q.val)
  rw [projected_part,on_part,projected_part,mul_sum]
  refine sum_congr rfl fun Q hit=>?_
  have sub:Painted.faithful Q ∧ Q.image Prod.fst=q.val := (mem_filter.mp hit).2
  rw [on_part,←sub.2,Finset.prod_image sub.1]
  rfl

variable {G:Gauge} {n:Side} (R:Rep G n) (o:V → Site n) (E:Support n → Config G n → Marker.Poly (Stock.census V))
variable (K:Box n → Config G n → Marker.Poly (Stock.census V)) (birth:J → V) (v:J → Config G n → ℂ)
local notation "a₀" => (fun j:J=>newborn (birth j))
omit [Fintype J] in
theorem project_new (j:J) (c:ℂ) : Painted.project (Poly.send ((Stock.census (Ink V)).fire (a₀ j)) c)=Poly.send ((Stock.census V).fire (birth j)) c := by
  change Painted.project (Poly.send (tag {a₀ j}) c)=_
  rw [project_send {a₀ j} (by simp [Painted.faithful])]
  simp only [image_singleton]
  rfl

theorem project_physical_product (proper:Rough.Ledger o E K R.p.threshold) (Z:Config G n) :
    Painted.project (play R C (exclaim R.activities C+liftSheet K) (fun U=>∑ i,liftSheet E i U) Z*
      ∏ j,(1+Poly.send ((Stock.census (Ink V)).fire (a₀ j)) (v j Z)))=
    play R B (exclaim R.activities B+K) (fun U=>∑ i,E i U) Z*
      ∏ j,(1+Poly.send ((Stock.census V).fire (birth j)) (v j Z)) := by
  have vac (i:Box n) (U:Config G n):project (exclaim R.activities C i U)=exclaim R.activities B i U := by
    change Painted.project (Poly.send (tag ∅) _)=_
    rw [project_send ∅ (by simp [Painted.faithful]),image_empty]
    rfl
  have nil:(∑ i,liftSheet E i Z).part (tag ∅)=0 := by
    rw [Poly.part_sum];exact sum_eq_zero fun i _=>(repaint_quiet _).trans ((proper.exp i).sil Z)
  rw [map_mul,map_prod,project_play _ _ _ _ nil]
  simp only [Pi.add_apply,map_add,map_sum,map_one,vac,liftSheet,project_repaint,project_new]
  rfl

end YM.Integration.InletSusceptibility.JointShadow
