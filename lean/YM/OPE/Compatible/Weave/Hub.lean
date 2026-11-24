import YM.OPE.Compatible.Weave.Rim
/-! # Wind basis matches Orthonormal continuum parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Flume.Page Prairies Maxwell Maxwell.Free Finset
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
open Shrew Saga Drift
include L a
lemma fauna_turn (s:Finset (Fin r))(p:Fin r→ Reed G)(x:Site n)(v:Ice G n):
     fauna (fun i j=>firm (p i) (p j)) (fun i=>fence (p i) (dart a x)) s (flo a v)= (∏ i∈s, Rate a (p i).1) * fauna (fun i j=>firm (Own a (p i)) (Own a (p j))) (fun i=> fence (Own a (p i)) x) s v:=by
       induction s using Finset.strongInduction with | _ s ih
       obtain rfl|he:=s.eq_empty_or_nonempty; simp only[fanE,Pi.one_apply,one_mul,Finset.prod_empty]
       let j:= s.min' he; let t:=s.erase j; have ht:t⊂s:= Finset.erase_ssubset (innerA he).1; let R(i):=Rate a (p i).1; have hp: (∏ i∈s,R i)=R j*∏ i∈t,R i:= (Finset.mul_prod_erase s R (innerA he).1).symm
       let g(i):= Own a (p i); let f(S'):=(fauna (fun i j=>firm (g i) (g j)) (fun i=>fence (g i) x) S') v
       rw [pier _ _ (innerA he), Pi.sub_apply, Pi.mul_apply, redoP, φ_zt, ih _ ht]; -- maybe wrong pier rhs
       rw [show (∏ i∈s,Rate a (p i).1)= _ from hp, pier (fun i j=>firm (g i) (g j)) (fun j=>fence (g j) x) (innerA he)]
       rw [Pi.sub_apply, Pi.mul_apply,mul_sub]; simp_rw [Finset.sum_apply,Pi.smul_apply,Finset.mul_sum]
       apply congr_arg₂ (·-·)
       · change R j*_ *(_*f t)= R j*_*(_*f t) -- products assoc? 
         ac_rfl
       apply Finset.sum_congr rfl; intro i hi; rw [ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset i t) ht), show firm (p (s.min' he)) (p i)= _ from firmQ (L:=L) a (p j) (p i), ← Finset.mul_prod_erase t R hi]; simp only[smul_eq_mul]; change R j*R i*firm (g j) (g i) *( _*f _)= R j*(R i*_) * (firm (g j) (g i) *f _); ring
lemma CarrierFlip (p: Saga G e k)(x:Site n)(v:Ice G n):Phi p firm (fun i=> fence i (dart a x)) (flo a v)=Phi (turnT a p) firm (fun i=> fence i x) v :=by
       induction p with 
       | mon i h hp=> exact fauna_turn (L:=L) a Finset.univ i x v 
       | empty=>rfl
       |  add A B I D=> exact congr_arg₂ (·+·) I D
       |  sml k A I=> exact congr_arg (k*·) I
omit L in
lemma Compass (q: Seat k m (Shade G))(x: Site n) (v:Ice G n):Strike k (worldR m k x (Shade G) (crew a G k m q)) v= Strike k (worldR m k (dart a x) (Shade G) q) (flo a v):=by
       obtain ⟨v,rfl⟩:= (spool G n).surjective v; rw [← F_legB]; simp_rw [← cadillac]; apply Finset.sum_congr rfl; intro i _; unfold Flume.Script.value;rw [railZ]; exact rightS a _ _ (fun _=>v)
lemma Eager (q:Seat k m (Shade G))(p:Saga G e k)(x:Site n)(H:∀ y:Site n, Strike k (worldR m k y _ q)=Phi p firm (fun v=> fence v y)):Strike k (worldR m k x _ (crew a G k m q))=Phi (turnT a p) firm (fence · x):=funext fun i=> (Compass ..).trans ( (congr_fun (H (dart a x)) (flo a i)).trans (CarrierFlip (L:=L) ..))
end YM.OPE.Quit
