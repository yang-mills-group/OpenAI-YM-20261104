import YM.AllOrder.Ink.Field
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
section algebra2
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
structure LinTest (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](k:ℕ)(F:(X→ℝ)→ℝ):Prop where
 add (f g) : Rank X k f→Rank X k g→F (f+g)=F f+F g
 scale f (r:ℝ) :Rank X k f→ F (r•f)=r*F f
variable {F : (X→ℝ)→ℝ}
lemma LinTest.finiteTest {ι:Type*}(s:Finset ι)(h:LinTest X k F)(v:ι→X→ℝ) (hf:∀ i∈s,Rank X k (v i)): F (∑ i∈s,v i)=∑ i∈s,F (v i) := by induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact (zero_smul ℝ (0:X→ℝ)) ▸ (h.scale _ 0 (Rank.nil k 0)).trans (zero_mul _)
 | insert i s hi ih=> have hF:= fun j hj=> hf j (mem_insert_of_mem hj); rw [Finset.sum_insert hi,Finset.sum_insert hi,h.add (v i) _ (hf i (mem_insert_self ..)) (Rank.sum hF),ih hF]
lemma LinTest.eval (k:ℕ) (x:X) : LinTest X k (fun f=> f x):= ⟨fun _ _ _ _=>rfl,fun _ _ _=>rfl⟩
variable [FiniteDimensional ℝ X]
open GaussianScore
lemma LinTest.deriving (F : (X→ℝ)→ℝ)(x:X)(h:LinTest X (k-1) F): LinTest X k (F ∘ diff' x):= ⟨fun f g hf hg=>by unfold Function.comp; rw [adds hf.read hg.read,h.add (diff' x f) (diff' x g) (hf.der x) (hg.der x)],fun f r hf=> by unfold Function.comp; rw [scalars hf.read,h.scale (diff' x f) r (hf.der x)]⟩
end algebra2
namespace Field
variable {A:Field α}(h:A.Good a C k) (hb:0≤a)(z:Site n)
local notation "P"=>rule α n
local notation "Fg"=>Frame (Leaf n α) k
def numbers (i : Frame (Leaf n α) k) :ℝ:= ∑' j:A.Ty, @ite ℝ (i=figure h z j) (Classical.propDecidable _) (A.fee j) 0
include h hb
lemma landing : A.site n z=∑ i: Frame (Leaf n α) k,numbers h z i • fun x:P=> paid x i.val:= by
   funext i; rw [Finset.sum_apply]; unfold numbers; exact (bookwise A.fee (fun j:Fg=>paid i j.val) (figure h z) (cash hb h)).tsum_eq
lemma Good.site : Prices k C (A.site n z):= by
   refine ⟨h.nonneg, ?_, ?_⟩; · rw [landing h hb z]; refine Rank.sum fun i _=> ((frame_cost i.val).2.1.up i.property).scal _
   intro x; have hh:=h.earns hb z x; refine (norm_tsum_le_tsum_norm hh.2.1).trans (hh.2.2.trans_eq (mul_comm ..))
lemma Good.binding : Prices k ((Fintype.card (Site n):ℝ)*C) (A.table n):= by
   let F z:=h.site hb (z:= (z:Site n)); have ht:= price_sum Finset.univ (fun i _=>F i); rw [sum_const,card_univ,nsmul_eq_mul] at ht; exact ht

lemma Good.tests {F:(rule α n→ℝ)→ℝ}(hF:LinTest _ k F): HasSum (fun i=> A.fee i*F (invoice z (A.slip i))) (F (A.site n z)):= by
   have hz (i:Fg):= (frame_cost i.val).2.1.up i.property; rw [landing h hb z, hF.finiteTest _ _ (fun i _=> (hz i).scal _)]; simp_rw [(show ∀ b:Fg,F (numbers h z b• fun x:P=>paid x b.val)=numbers h z b*F (fun x=>paid x b.val) from fun i=>hF.scale _ _ (hz i))]; exact bookwise A.fee (fun j:Fg=>F (fun x=>paid x j.val)) (figure h z) (cash hb h)
end Field
end YM.AllOrder.Ink
