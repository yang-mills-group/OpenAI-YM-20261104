import YM.FormalOPE.RG10.MarkovChain.Line
/-!
 # immediate field semantics at canonical multi-chart truss: additive roof of price jets

 Out-of-window estimates & Stencil.C costs not from here. This is actual proof that
 Φ's quadratic precision and log-weight jets are banded w.r.t. time in the history
 (at this regulator only). Important not assuming that all future-state costs can be
 eliminated by order signs; characterize by comparing two future fields with same head.
 Real working.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Line
variable {G: Gauge}{c f n:Side}

variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val){L: Fabric G c} {T: L.loom.Truss}
variable {β:Type}
 def Heads {L:Fabric G n} (T:L.loom.Truss)(f:Field T→β): Prop:= ∀ x y, send T x=send T y→ f x=f y
variable (P:Inside S.ratio)
local notation "d" => sector S H t hf L P T
 def enduring (a : Field (P.join T H t hf)→ ℝ) (y: Field T): ℝ:= a (d (0,y))
 def Near (a: Field (P.join T H t hf)→ℝ)(x: Cross (G:=G) S P) : Prop:= Heads T (fun y=> a (d (x,y))-enduring S H t hf P a y)
-- recursively price dependence criterion. terminal all.
 def Roof {n:Side}{L: Fabric G n} (K: Cloth L) (a: Field K.choose→ℝ): Prop:= match K with
 | .floor _ _ _=> True
 | .inLayer (S:=S) (b:=H) (t:=t) (h:=hf) P K => (∀ x,Near S H t hf (T:=K.choose) P a x) ∧ Roof K (enduring S H t hf P a)

variable {Z:Fabric G n}
namespace Roof
local notation "Y"=> P.join T H t hf
lemma constant {n: Side} {Z:Fabric G n}(K:Cloth Z)(s:ℝ): Roof K fun _=>s:=by
 cases K with
 | floor=> trivial
 | @inLayer c f S H t hf L P K=> exact ⟨fun x y z _=>rfl,constant K s⟩
termination_by structural K
lemma head {K:Cloth Z} {a:Field K.choose→ℝ}(h:Heads K.choose a):Roof K a:= by
 cases K with
 | floor=> trivial
 | @inLayer c f S H t hf L P K=>
    let D:=sector S H t hf L P K.choose
    refine ⟨fun x y z _=>?_,?_⟩
    · change a (D _) - a (D _) = a (D _) - a (D _)
      exact congr_arg₂ (· - ·) (h _ _ (show send (P.join K.choose H t hf) (D (x,y))=send (P.join K.choose H t hf) (D (x,z)) from by unfold D; simp)) (h _ _ (by unfold D; apply Eq.trans (Line.first ..); exact (Line.first S H t hf L P K.choose 0 z).symm)) -- definitional rw
    have he: enduring S H t hf (T:=K.choose) P a = fun _=> a 0:= funext (fun y=> h _ _ (show send (P.join K.choose H t hf) (D (0,y))= _ from by unfold D; rw [Line.first]; simp; rfl))
    rw [he]; exact constant K _
lemma add {n:Side}{Z:Fabric G n}{K:Cloth Z} {a b:Field K.choose→ℝ}(ha: Roof K a)(hb: Roof K b): Roof K (a+b):= by
 cases K with
 | floor=> trivial
 | @inLayer c f S H t hf L P K=>
    rw [Roof] at ha hb ⊢
    let A:=enduring S H t hf (T:=K.choose) P a; let B:= enduring S H t hf (T:=K.choose) P b; let D:= sector S H t hf L P K.choose
    refine ⟨fun x y z h=> ?_,(add (a:=A) (b:=B) ha.2 hb.2)⟩
    have hu: a (D (x,y))-A y= a (D (x,z))-A z:= ha.1 x y z h
    have hv: b (D (x,y))-B y= b (D (x,z))-B z:= hb.1 x y z h
    change a _ + b _ - (A _+ B _) = a _+b _-(A _+B _); linarith
termination_by structural K
lemma smul {n:Side}{Z:Fabric G n}{K:Cloth Z} {a:Field K.choose→ℝ}(ha: Roof K a)(r:ℝ): Roof K (r • a):= by
 cases K with
 | floor=> trivial
 | @inLayer c f S H t hf L P K=>
    rw [Roof] at ha ⊢; refine ⟨fun x y z hw=> ?_,(smul (a:=enduring S H t hf (T:=K.choose) P a) ha.2 r)⟩
    have he:= ha.1 x y z hw; change r * _-r * _= r*_ - r * _; rw [← mul_sub, ← mul_sub]; exact congr_arg (r * ·) he
termination_by structural K
lemma neutral (K:Cloth Z): Roof K 0:= constant K 0
lemma billSum {K:Cloth Z}{J:Type}(s:Finset J)(a:J→ Field K.choose→ℝ)(h:∀ x∈s, Roof K (a x)): Roof K (∑ i∈s,a i):= by induction s using Finset.induction with
                                                                                                                                 | empty=> simp only [Finset.sum_empty]; exact neutral _
                                                                                                                                 | insert i s q ih=> rw [Finset.sum_insert q]; exact add (h i (by simp)) (ih (fun v hv=> h _ (by simp [hv])))
-- ascent helpers
variable (K:Cloth L)
lemma onlyNow (a) (h:∀ x, Heads K.choose (fun (v:Field K.choose)=> a (sector S H t hf L P K.choose (x,v)))) : Roof (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P K) a:= by
 refine ⟨fun x y z H=> ?_,Roof.head (a:=enduring S H t hf (T:=K.choose) P a) (h 0)⟩
 exact congr_arg₂ (·-·) (h x y z H) (h 0 y z H)
lemma liftLater (a:Field K.choose→ℝ) (h:Roof K a): Roof (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P K) (fun x=> a (((sector S H t hf L P K.choose).symm x).2)):= by
 let Q:= sector S H t hf L P K.choose; -- d local notation conflict
 rw [Roof]; refine ⟨fun x y z _=>?_,?_⟩
 · unfold enduring; simp
 change Roof K (enduring S H t hf P (fun (x:Field (P.join K.choose H t hf))=> a ((Q.symm x).2)))
 rw [show enduring S H t hf P (T:=K.choose) (fun x=> a ((Q.symm x).2))=a from funext fun i=> by simp [enduring,Q]]
 exact h
end Roof
end YM.FormalOPE.RG10.MarkovChain
