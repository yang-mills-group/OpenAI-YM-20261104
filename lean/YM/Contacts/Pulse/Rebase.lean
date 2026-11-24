import YM.Contacts.Pulse.Atlas
import YM.Contacts.Pulse.Winding
/-! Deck transitivity. Periodization at one lift produces at all roots. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG MergeProof Push.AbsoluteSums
open scoped Classical BigOperators Topology NNReal
universe u v w
variable {ι X Y T Z W:Type*}

structure Gaugeway (p:X→Y)(T:Type*) [Group T] [MulAction T X] : Prop where
  fixed z (a:T) : p (a • z)=p z
  lifts x y: p x=p y→∃ t:T,t • x=y
  mono (x:X) : Injective fun t:T=> t • x
  onto : Surjective p

def Mirrored (e:Equiv.Perm X) (G:Field ι X) : Prop := ∀ x,G (e∘x)=G x
variable [Group T] [MulAction T X] {p:X→Y}

def Carried (T:Type*) [Group T][MulAction T X] (G:Field ι X) := ∀ (t:T) (x:ι→X), G (fun i=>t • x i)=G x
-- equivalence between fibers of a tuple at distinct anchors by unique transport
namespace Gaugeway
variable {F:Field ι X}(g:Gaugeway p T)
def send (g:Gaugeway p T)(x y:X): T:= if h:p x=p y then (g.lifts x y h).choose else 1
lemma send_across (x y:X)(h:p x=p y): g.send x y • x=y:= by rw [send,dif_pos h]; exact (g.lifts x y h).choose_spec
variable (a:ι→ Y)
abbrev Registry (i:ι)(x:X) := {q:Locked X i x// p ∘ q.val=a}
private lemma projected {i:ι}{x:X}(u: Registry (p:=p) a i x)(j:ι): p (u.val.val j)=a j:= congr_fun u.property j
variable {a}
def pilot (i j:ι){x z:X}(hz:p z=a j) (u:Registry (p:=p) a i x): Registry (p:=p) a j z :=
  let t:=g.send (u.val.val j) z
  ⟨⟨(fun k=>t • u.val.val k),g.send_across _ _ ((projected a u j).trans hz.symm)⟩, funext fun i=>Eq.trans (g.fixed ..) (projected a u i)⟩
lemma pilot_twice (i j:ι){x z:X}(hx:p x=a i)(hz:p z=a j) (u:Registry (p:=p) a i x): g.pilot j i hx (g.pilot i j hz u)=u:=by
  let s:=g.send (u.val.val j) z
  let t:=g.send (s • u.val.val i) x
  let Y:=g.pilot j i hx (g.pilot i j hz u)
  have hy (b:ι): Y.val.val b=t • s • u.val.val b:=rfl
  apply Subtype.ext; apply Subtype.ext; funext k
  calc Y.val.val k = (t*s) • u.val.val k := (hy k).trans (mul_smul ..).symm
       _ = u.val.val k := by have he : t*s=1:=g.mono (u.val.val i) ((mul_smul ..).trans ((hy i).symm.trans (Y.1.2.trans (by simp [u.1.2])))); rw [he,one_smul]
include g
lemma straight (h : Carried T F)(i j:ι){x z:X}(hx:p x=a i)(hz:p z=a j): Lay p F i x a = Lay p F j z a:=by
  let e : Registry (p:=p) a i x ≃ Registry (p:=p) a j z:=⟨g.pilot i j hz,g.pilot j i hx,g.pilot_twice i j hx hz,g.pilot_twice j i hz hx⟩
  unfold Lay; rw [← e.tsum_eq (fun u=>F u.val.val)]; apply tsum_congr; intro t; exact (h (g.send (t.val.val j) z) t.val.val).symm

def lower (g:Gaugeway p T)(F:Field ι X)[Nonempty ι] : Field ι Y := fun y=> let i:=Classical.arbitrary ι; Lay p F i (surjInv g.onto (y i)) y
lemma lower_shadow (h : Carried T F)[Nonempty ι]: Shadow p F (g.lower F):= fun i _ z=> (g.straight h _ i (rightInverse_surjInv g.onto _) z.property.symm).trans (roll_cram ..).symm

end Gaugeway

-- Invariance of operations with no decay hypotheses
section miracles
omit [Group T] [MulAction T X]
variable {κ:Type*}
lemma mir_loop {e:Equiv.Perm X}{F:Field (Option (Option ι)) X}{G:X→X→ℝ} (h : Mirrored e F)(hg:∀ x y,G (e x) (e y)=G x y): Mirrored e (loop G F):= by
  intro x; unfold loop; rw [←(Equiv.prodCongr e e).tsum_eq]; apply tsum_congr; rintro ⟨a,b⟩; change G (e a) (e b)* _=_; rw [hg]; apply congr_arg; rw [← h (vertex a (vertex b x))]; congr 1; funext t; rcases t with _|(_|x) <;> rfl
lemma mir_stitch {e: Equiv.Perm X}{G:X→X→ℝ} {F:Field (Option ι) X}{K:Field (Option κ) X}(h:∀ x y,G (e x) (e y)= G x y)(hf:Mirrored e F)(hk: Mirrored e K): Mirrored e (stitch G F K):= by
  intro x; unfold stitch; rw [←(Equiv.prodCongr e e).tsum_eq]; apply tsum_congr; rintro ⟨a,b⟩; change _*G (e a) (e b)*_=_; rw [h, ←hf (vertex a (x∘Sum.inl)), ←hk (vertex b (x∘Sum.inr))]; congr 2
  · apply congr_arg F; funext t; cases t<;>rfl
  funext t; cases t<;>rfl
lemma mir_allAt [Fintype ι]{e:Equiv.Perm X}{F:Field ι X}{G:ι→ X→Y→ℝ}{d:Equiv.Perm Y} (h:Mirrored e F)(hg:∀ i x y,G i (e x) (d y)=G i x y) : Mirrored d (allAt G F) := by
  intro x; unfold allAt; rw [← (Equiv.arrowCongr (Equiv.refl _) e).tsum_eq]; apply tsum_congr; intro t; rw [show (Equiv.arrowCongr (Equiv.refl _) e) t=e∘ t from rfl,h]; simp only [Function.comp_apply,hg]
end miracles
end YM.Pulse
