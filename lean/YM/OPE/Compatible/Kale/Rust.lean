import YM.OPE.Compatible.Kale.Git
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
open Nestle StageLight Shrew Balsam
variable {U:Gloam}(H:∀ i,Even (U.M i).val)(V:Nestle.Crew U)
abbrev Grn:= IpT H G
lemma Tar₁ :Tar (U:=U) H (G:=G) 1:=by rw [show (1:IpT H G)=shucks H [] from funext fun j=>funext fun i=>by simp [shucks]]; exact Tar.monom _
lemma TarZ :Tar H (G:=G) 0:=by simpa using (Tar.scale (H:=H) 0 (Tar₁ (G:=G) H))
lemma PinTar (s: Finset I)(X:I→ IpT H G)(h:∀ i∈s,Tar H (X i)): Tar H (∑ i∈s,X i):=by induction s using Finset.induction with | empty=> rw [Finset.sum_empty]; exact TarZ H | insert a s ha ih=> rw [Finset.sum_insert ha]; exact Tar.add (h a (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma PTar (v:Page (Shade G) r): Tar H (fun i x=> render (V.val i) v (fun _=>spool G _ (cloak (H i) x))):=by
    let A(j:Fin r):Yarn U G:=⟨V,(v j).2.2,(v j).2.1,(v j).1⟩; let y:=List.ofFn A
    rw [show (fun i:ℕ=> _)= shucks H y from ?_]; exact Tar.monom _
    funext i x; have hp (j: Fin r): slips H (A j) i x=(spool G _ (cloak (H i) x) ((V.val i)+wrap _ ((v j).1),(v j).2)):=rfl
    unfold render shucks; change (∏ j:Fin r,(spool G _ (cloak (H i) x) _))= _; let Y(t:Yarn U G):ℝ:= slips H t i x; change (∏ j:Fin r,_)=∏ j:Fin y.length,Y (y.get j); simp_rw [← hp]; exact matchC r Y A y rfl
where matchC (r:ℕ)(Y:Yarn U G→ℝ)(A:Fin r→ Yarn U G)(l:List (Yarn U G))(h:l= List.ofFn A):(∏ j:Fin r,Y (A j))= ∏ j:Fin l.length,Y (l.get j):=by
         have ht:r=l.length:=by simp [h]
         subst r; congr 1; funext i; have hv:A i = l.get i:=by simpa [List.get_eq_getElem] using congr_arg (fun L:List (Yarn U G)=> L[i.val]?.getD (A i)) h.symm
         rw [hv]
lemma cashH {p: Script (Shade G) r}(hp:Brief p): Tar H (fun i x=> scribe (V.val i) p (fun _=>spool G _ (cloak (H i) x))):=by
      obtain ⟨s,hs⟩:=hp
      let X(t:Page (Shade G) r):IpT H G:= fun i x=> p t* render (V.val i) t (fun _=>spool G _ (cloak (H i) x)); refine (_root_.cast (congr_arg (Tar H) ?_) (PinTar H s X (fun i _=>Tar.scale (p i) (PTar H V i)))); funext i x; unfold scribe; rw [Finset.sum_apply, Finset.sum_apply]; exact (tsum_eq_sum (fun i hi=>by unfold X;rw [hs _ hi,zero_mul])).symm
abbrev Vtap (p: Tower (Shade G) d τ) (x:Site c):= inkM (spread G d τ p) d x
lemma tip_tap (p:Tower (Shade G) d τ)(hp:twilight p)(j:Phase): Tar H (fun i x=>(Vtap p (V.val i) (cloak (H i) x)).seq j.val):=by
     unfold Vtap; simp_rw [vein_i]; let f(t:ℕ):IpT H G:=fun i x=> value (V.val i) (Drift.spread G d τ p j t) (spool G _ (cloak (H i) x)); refine cast (congr_arg (Tar H) ?_) (PinTar H (Finset.range (d+j.val+1)) f fun i _=> cashH H V (hp j i)); funext i x; rw [Finset.sum_apply, Finset.sum_apply];rfl
variable {H}
lemma alpha_eq {p: Tower (Shade G) d τ}(B:Saga G e k)(h:∀ (n:Side)(x:Site n), Strike (d+(0:Phase).val) (worldR (τ 0) _ x _ (p 0))= Phi B firm (fence · x)) {U':Even n.val}(x:Site n)(v:Libra.Keys G (Weir.Limb U')):
     (Wish B U' x v)= (Vtap p x (cloak U' v)).s:=by
         have hz :Vtap p x= _ := (by unfold Vtap;rfl : Vtap p x = inkM (Drift.spread G d τ p) d x)
         have hp : Strike (d+(0:Phase).val) (worldR (τ 0) (d+(0:Phase).val) x _ (p 0)) (spool G _ (cloak U' v))= (Vtap p x (cloak U' v)).s:=by rw [← cadillac (k:=d+(0:Phase).val) (x:= (p 0)) (m:=τ 0)]; rfl
         have ht:= h n x; rw [ht] at hp; rw [← hp]; clear hp ht h; induction B with
         | @mon i A h hs=>
           have h(E:Finset (Fin i)): fauna (fun i j=>firm (A i) (A j)) (fun i=> fence (A i) x) E (spool G _ (cloak U' v))=fauna (fun i j=>firm (A i) (A j)) (fun i=>poseT U' x (A i).2 (A i).1) E v :=by
              induction E using Finset.strongInduction with | _ s ih
              obtain rfl|hh:=s.eq_empty_or_nonempty; · rw [fanE,fanE];rfl
              let a:=s.min' hh; have he:= Finset.erase_ssubset (innerA hh).1; rw [pier _ _ (innerA hh), pier _ (fun i=>poseT U' x (A i).2 (A i).1) (innerA hh), Pi.sub_apply, Pi.sub_apply, Pi.mul_apply, Pi.mul_apply, ih _ he, show fence (A (s.min' hh)) x (spool G n (cloak U' v))= _ from in_fields U' (A a) x v, Finset.sum_apply, Finset.sum_apply]; apply congr_arg₂ (·-·); rfl; apply Finset.sum_congr rfl; intro j _; exact congr_arg (fun y:ℝ=> firm (A a) (A j) • y) (ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) he))
           exact (h _).symm
         | add X Y I O=> exact congrArg₂ (·+·) I O
         | sml x y I=> exact congrArg (x • ·) I
         | empty=>rfl
end YM.OPE.Quit
