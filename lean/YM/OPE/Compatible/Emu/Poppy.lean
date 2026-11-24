import YM.OPE.Compatible.Emu.Glob
import YM.OPE.Compatible.Emu.Queues
/-!
# Gauge direction on national patch. All int variation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter Lattice Laurent Wilson Matrix RG Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open Finset
variable {r s m i b k:ℕ}{n:Side}{G:Gauge} {p:ℤ}{x y: Site n}
-- gradient shifts for table.All stencils
noncomputable def vertQ (r:ℕ)(x:Site n):ℕ:=if pdist x ≤ r then (((r:ℤ)+1)- lift x perch).toNat else 0
lemma elevator (hp:Board n (r+1))(x:Site n)(he:pdist x ≤ r): vertQ r x=vertQ r (x+step perch)+1:=by
       let y:=x+step perch; let a:= lift x; let d:=a+step perch; have hX:a∈Lattice.box r:=(lift_le x).mp he; have hy:d∈Lattice.box (r+1):=(up a _ hX).1; have ht:y=wrap n d:=by simp only [y,d,a,map_add,wrap_lift,wrap_step]
       have hv:lift y=d:=by rw [ht]; exact level hp hy
       have hb:d perch=a perch+1:=by simp[d]
       change vertQ r x=vertQ r y+1; unfold vertQ; rw [if_pos he,hv]; change (↑r+1- a perch).toNat = _; have hh:= (box_test.mp hX).2 perch; split_ifs with hz; · omega
       have hl:a perch=(r:ℤ):=by
          by_contra h; apply hz; rw[lift_le,hv, box_test]; obtain ⟨hI,hJ⟩:=box_test.mp hX; constructor<;>intro i<;>specialize hI i<;>specialize hJ i<;> by_cases hs:i=perch<;>first| (subst i; omega)|(rw [show d i=a i from plane a _ _ (Ne.symm hs)]; omega)
       omega
noncomputable def strung {r:ℕ} (U: Config G n) (x:Site n): G.El:=(travel U x (List.replicate (vertQ r x) (posDir perch)))⁻¹ -- implicit r? not included!
lemma stringK (U:Config G n)(x:Site n)(hx:¬pdist x ≤ r):strung (r:=r) U x=1:=by unfold strung; rw [vertQ,if_neg hx,List.replicate_zero,travel,inv_one]
lemma stringT (hp:Board n (r+1))(U:Config G n)(x:Site n)(he:pdist x ≤ r): strung (r:=r) U x * U (x,perch)=strung (r:=r) U (x+step perch):=by unfold strung; rw[elevator hp x he,List.replicate_succ,travel,Step.vec_pos,Step.pos_read]; group
lemma tipAt (hp:Board n (r+1)) (U:Config G n)(x:Edge (Site n))(he:x∈ mesa r n): Lattice.gauge (strung (r:=r) U) U x=1:=by
       obtain ⟨i,hi,rfl⟩:=mem_image.mp he; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; unfold Lattice.gauge; rw [show _ * U _ = _ from stringT hp U (wrap n a) (aery (tip hp (Nat.le_succ _)) ha),mul_inv_cancel]; -- unif
lemma Mov (hp:Board n (r+1)) (U V:Config G n): ∃ t:Site n→ G.El,(∀ i,r < pdist i→ t i=1) ∧ ∀ i∈mesa r n, Lattice.gauge t U i=V i:=by
        let A:= strung (r:=r) U; let B:= strung (r:=r) V; refine ⟨B⁻¹*A,(fun i hi=>show (B i)⁻¹*A i=1 from by unfold A B; rw[stringK _ _ hi.not_ge,stringK _ _ hi.not_ge];simp),?_⟩; intro i hi
        have he: V i=(B i.1)⁻¹*(Lattice.gauge B V i)*B (dotUp i):=by unfold Lattice.gauge dotUp; group
        have hv: Lattice.gauge (B⁻¹*A) U i=(B i.1)⁻¹* (Lattice.gauge A U i) *B (dotUp i):=by unfold Lattice.gauge; simp only [Pi.mul_apply,Pi.inv_apply,dotUp]; group
        rw [tipAt hp _ i hi] at he; rw[tipAt hp _ i hi] at hv; exact hv.trans he.symm
lemma castQ (r:ℕ)(h:Board n (r+1))(i:Edge Cover)(he:i∈Delta r): lift ((Moor i n).1+step i.2)=dotUp i ∧ lift (Moor i n).1=i.1:=by
        have hv: (Moor i n).1+step i.2=wrap n (dotUp i):= (pier i).symm; exact ⟨(congr_arg _ hv).trans (level h (arcP he).2),level h (arcP he).1⟩
-- exterior free set.Every route.Read before arity
end YM.OPE.Merchant
