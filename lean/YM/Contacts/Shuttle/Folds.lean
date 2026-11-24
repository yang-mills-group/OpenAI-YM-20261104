import YM.Contacts.Shuttle.Water
import YM.Contacts.Pulse.Jacket
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle.Trace
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin
open Milling Milling.Steam Milling.Forge Tensor MultiNext.SignedSource Pattern Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {G:Gauge}{b h d k r n:ℕ}{X Y:Type}
abbrev Hood (k:ℕ)(X:Type):=Fin k→X
abbrev lap (v:Tailor k)(i:Fin k):Cover:= fun j=>v (i,j)
def books (z:Tailor k)(f:Fin k→E4→ℝ):= ∏ i, f i (xyz (lap z i))
def Throng (h k:ℕ) : Submodule ℝ (Tailor k→ℝ):= Submodule.span ℝ {x|∃ (f:Fin k→E4→ℝ)(j:Fin k→ℕ), (∀ i,f i∈ Powers.space E4 ℝ (j i)) ∧ (∑ i,j i) ≤ h ∧ x=fun z=> books z f}
namespace Quill
lemma widen (k:ℕ) (h: b≤d) : Throng b k ≤ Throng d k:=Submodule.span_mono (fun f ⟨F,j,hF,hj,hT⟩=>⟨F,j,hF,hj.trans h,hT⟩)
lemma origin (x:E4)(p:E4→ℝ)(hp:p∈ Powers.space E4 ℝ h): (fun z=> p (z+x))∈ Powers.space E4 ℝ h:= by rw [show (fun z=> p (z+x))=(fun z=>p (z+x)-p z)+p from funext (fun z=>(sub_add_cancel (p (z+x)) (p z)).symm)]; exact (Powers.space ..).add_mem (Powers.widen _ _ (Nat.sub_le h 1) (Powers.discrete x hp)) hp
lemma axisCost (a:Axis)(p:E4→ℝ)(hp:p∈ Powers.space E4 ℝ h): (fun z:E4=> (z a)*p z)∈ Powers.space E4 ℝ (h+1):= by
    rw [add_comm h]; refine Powers.genie (ContinuousLinearMap.mul ℝ ℝ) (f:=fun z:E4=> z a) (Powers.residence ?_ (le_refl 1)) hp; exact ⟨(EuclideanSpace.proj (𝕜:=ℝ) a).contDiff,fun x v=>by simp⟩ -- use ContDiff
-- translation all
lemma afloat (v:Tailor k)(f:Tailor k→ℝ)(h:f∈ Throng b k): (fun z=> f (z+v))∈ Throng b k:= by
   refine Submodule.span_induction (p:=fun f _=> (fun z=>f (z+v))∈ Throng b k) ?_ ((Throng ..).zero_mem) (fun _ _ _ _ h ht=> (Throng ..).add_mem h ht) (fun r _ _ h=>(Throng ..).smul_mem _ h) h
   rintro f ⟨g,j,hg,hj,rfl⟩; refine Submodule.subset_span (Set.mem_setOf.mpr ⟨fun i z=>g i (z+xyz (lap v i)),j,fun i=> origin _ _ (hg i),hj,funext fun x=>?_⟩); unfold books; exact prod_congr rfl (fun i _=> congr_arg (g i) (by ext a; change (((x (i,a)+v (i,a):ℤ):ℝ))= (x (i,a):ℝ)+(v (i,a):ℝ);simp))
lemma accost (a:Keys k)(f:Tailor k→ℝ)(h:f∈ Throng b k): (fun z=> (z a:ℝ)*f z)∈Throng (b+1) k:= by
   let A:=Throng (b+1) k; refine Submodule.span_induction (p:=fun f _=> (fun z:Tailor k=>(z a:ℝ)*f z)∈ A) ?_ ?_ ?_ ?_ h
   · rintro f ⟨g,j,hg,hj,rfl⟩; rcases a with ⟨t,a⟩; let u (x:E4):= x a*g t x; refine Submodule.subset_span (Set.mem_setOf.mpr ⟨update g t u,update j t (j t+1),fun i=>?_ ,?_, funext fun x=>?_⟩)
     · by_cases he:i=t; rw [he,update_self,update_self]; exact axisCost _ _ (hg _); rw [update_of_ne he,update_of_ne he]; apply hg
     · rw [← add_sum_erase (a:=t) univ (update _ _ _) (mem_univ _), update_self]; rw [← add_sum_erase univ j (mem_univ t)] at hj; rw [sum_congr rfl (fun i hi=> update_of_ne (mem_erase.mp hi).1 ..)]; omega
     unfold books; dsimp only; rw [← mul_prod_erase _ (fun i=>g i (xyz (lap x i))) (mem_univ t),← mul_prod_erase _ (fun i=>update g t u i (xyz (lap x i))) (mem_univ t), update_self] -- remove
     rw [← mul_assoc]; apply congr_arg₂ (·*·) rfl; apply prod_congr rfl; intro i hi; rw [update_of_ne (mem_erase.mp hi).1]
   · simpa [Pi.zero_def] using (A.zero_mem)
   · intro x y _ _ hx hy; simp only [Pi.add_apply, mul_add]; exact A.add_mem hx hy
   intro r y _ hy; simp_rw [Pi.smul_apply,smul_eq_mul, mul_left_comm _ r]; exact A.smul_mem _ hy
lemma pier (m:ℕ)(f:Tailor k→ℝ): Spine.Quill.piece m f∈ Throng m k:= by
   induction m generalizing f with
   | zero=>
      have he : (fun _ : Tailor k => (1:ℝ))∈Throng 0 k:= Submodule.subset_span (Set.mem_setOf.mpr ⟨fun _ _=>1,fun _=>0,fun _=>Powers.constants _ _, by simp,funext fun i=>by simp [books]⟩)
      rw [show Spine.Quill.piece 0 f=(f 0) • _ from (show _=(f 0) • (fun _ : Tailor k=>(1:ℝ)) from funext (fun i=> by simp [Spine.Quill.piece]))]; exact (Throng ..).smul_mem _ he
   | succ m ih =>
      let V:= Throng (m+1) k; let p (i:Keys k)(x:Tailor k):=(x i:ℝ)*Spine.Quill.piece m (Spine.Quill.jump i f) (x+ -arc i); rw [show Spine.Quill.piece (m+1) f=((m:ℝ)+1)⁻¹ • ∑ i,p i from funext fun x=>by simp [p,sub_eq_add_neg,Spine.Quill.piece,Finset.sum_apply]]; exact V.smul_mem _ (V.sum_mem fun i _=> accost i _ (afloat (-arc i) _ (ih _)))
lemma whist (f:Tailor k→ℝ)(m:ℕ): Spine.Quill.zen m f∈ Throng (m-1) k:= by rw [show Spine.Quill.zen m f= ∑ i∈Finset.range m, Spine.Quill.piece i f from funext (fun i=>by rw [Finset.sum_apply];rfl)]; exact (Throng ..).sum_mem fun i hi=> widen k (by have ht:= mem_range.mp hi; omega) (pier i f)
end Quill
end YM.Contacts.Shuttle.Trace
