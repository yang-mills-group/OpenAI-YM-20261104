import YM.MS.Cylinder.Orbit
import YangMills.WilsonProof.NativeSupport.YM.MS.KoszulIndex
import YM.MS.Cylinder.Shadow
/-!
# Stencil symmetry charges

At any fixed rank or ghost channel. Burden ranks use another lemma. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Lab
open Function Filter Set Finset Plane Koszul
variable {A P I : Type*}{s p q : Sector A} {F G : Seed A P ℂ} {m:A→ℤ}{h h':ℤ}

structure Tune (p:Sector A)(m:A→ℤ)(h:ℤ)(F:Seed A P ℂ): Prop where
   symm : Symm (field p) F.val
   ghost : Rails (m ∘ Prod.fst) h F.val
   still : Still F.val
namespace Tune
lemma zero : Tune p m h (0:Seed A P ℂ):= ⟨Symm.zero,Rails.zero,Still.zero⟩
lemma add (he:Tune p m h F)(hp:Tune p m h G): Tune p m h (F+G):= ⟨he.symm.add hp.symm,he.ghost.add hp.ghost,he.still.add hp.still⟩
lemma sub (he:Tune p m h F)(hp:Tune p m h G): Tune p m h (F-G):= ⟨he.symm.sub hp.symm,he.ghost.sub hp.ghost,he.still.sub hp.still⟩
lemma cash (c:ℂ)(hc:star c=c)(hF:Tune p m h F): Tune p m h (c • F):= ⟨hF.symm.smul _,hF.ghost.smul _,hF.still.scalar _ hc⟩
lemma sum {p:Sector A}{F:I→Seed A P ℂ}(J:Finset I)(H:∀ i∈J,Tune p m h (F i)): Tune p m h (∑ i∈J,F i):= by
   refine ⟨?_,?_,?_⟩ <;> rw [sum_stack]; exact Symm.sum _ fun i hi=>(H i hi).symm; exact Rails.sum _ fun i hi=> (H i hi).ghost; exact Still.sum _ fun i hi=> (H i hi).still
lemma enter (he:Tune p m h F)(i:Mode A P): Tune p m (h-m i.1) (enter i F):= ⟨he.symm.drop _,he.ghost.enter _,he.still.D _⟩
lemma twisted (he:Tune p m h F)(c:Bool): Tune p m h (twisted (field p) c F):= ⟨he.symm.signs _,he.ghost.sign _,he.still.sign _⟩
lemma pair (he:Tune p m h F)(hp:Tune p m h' G): Tune p m (h+h') (couple (field p) F G) := ⟨he.symm.times hp.symm,he.ghost.product hp.ghost,he.still.product hp.still⟩
lemma lit (i:Mode A P): Tune p m (m i.1) (Cylinder.single i):= ⟨speaks_s _, Rails.letter i, Still.letter i⟩
lemma move {Q:Type*}(r:P→Q)(he:Tune p m h F): Tune p m h (transport r F):= ⟨(move_tie _).sym F he.symm,he.ghost.ferry (v:=m∘Prod.fst) (post r) (fun _=>rfl) _, he.still.passes (post r) F⟩
lemma parity (hp:Tune p m h F)(h':∀ a,Local.parity (m a)=p a): Pure (field p) (Local.parity h) F.val:= hp.ghost.parity (fun i=> h' i.1)
lemma heart (he:Tune p m h F)(i j:A): Tune p m (h-m i-m j) (heart i j F):= by obtain ⟨s,hs⟩:= obliges F; rw [heart_by _ _ F hs]; exact sum _ fun y hy=> (he.enter (i,y)).enter (j,y)

variable [AddCommGroup P]
lemma force (he:Tune p m h F)(i:A)(x:P): Tune p m (h-m i) (force i x F):= by obtain ⟨s,hs⟩:= obliges F; rw [force_at F hs]; exact sum _ fun y _=> (he.enter (i,y)).move (fun z=> (x-y)+z)
lemma root (he:Tune p m h F)(hv:Tune p m h' G)(i j:A): Tune p m (h+h'-m i-m j) (root p i j F G):= by
   obtain ⟨s,hs⟩:= obliges G; rw [root_at F G i j hs]; refine sum _ (fun x _=> ?_); rw [spot_eq]; apply add
   · rw [show h+h'-m i-m j=(h-m i)+(h'-m j) by omega]; exact ((he.force i _).twisted _).pair (hv.enter (j,x))
   rw [show h+h'-m i-m j=(h-m j)+(h'-m i) by omega]; exact ((he.twisted _).force j _).pair (hv.enter (i,x))

omit [AddCommGroup P] in
lemma self_cash (he:Tune p m h F) {c:Mode A P→ℂ}(h':∀ i,star (c i)=c i): Tune p m h (graffiti c F) := by
    refine ⟨fun l i j r=> ?_, he.ghost.tags _ F, Still.charges c h' he.still⟩; simp only [landc,rent,he.symm l i j r, List.map_append,List.map_cons,List.prod_append,List.prod_cons]; ring

variable [Fintype I](B:Bonded p I){u:ℤ}(hc:∀ i,m (B.dual i)+m (B.plain i)=u)
include hc
omit [AddCommGroup P] in
lemma lapped (hF:Tune p m h F): Tune p m (h-u) (B.Lap F):= by
    rw [B.lap_at]; refine sum _ (fun i _=> ?_); rw [← hc i]; have hs := hF.heart (B.dual i) (B.plain i); rw [← sub_sub] ; exact hs.cash _ (by cases he:p (B.plain i) <;> simp [Bonded.fee,cross,he])
lemma touch (hF:Tune p m h F)(hg:Tune p m h' G): Tune p m (h+h'-u) (B.touch F G):= by
    rw [B.touching]; refine sum _ (fun i _=> ?_); rw [← hc i,← sub_sub]; exact (hF.root hg _ _).cash _ (by cases he:p (B.plain i) <;> simp [Bonded.fee,cross,he])
end Tune
end YM.MS.Cylinder.Lab
