import YM.OPE.Compatible.Straws.Stoop
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
namespace Arc
open Flock
-- curly tokenization
abbrev jur (u:ℝ→Token):ℝ→ℝ:=fun i=>(u i).atK i
abbrev ski : Token:=⟨0,1,0⟩
lemma readsId : Reads (fun t:ℝ=>t) ski:= (Reads.stride (1:ℝ)).cong (Filter.Eventually.of_forall fun i=>by simp)
structure Fitted (p:ℝ→Token): Prop where
   A : Gael (fun i=>(p i).s)
   B : Gael (fun i=>(p i).l)
   C : Gael (fun i=>(p i).h)
def mine (p:ℝ→Token) : Token:= trill fun i=> (p i).atK i
abbrev assembleJ (u v w:Token):= u+ski*v+ski*ski*w
namespace Fitted
variable {p q:ℝ→Token}
lemma assent {s t w:Token}(h:Reads (fun i=>(p i).s) s)(ht:Reads (fun i=>(p i).l) t)(hv:Reads (fun i=>(p i).h) w): Reads (jur p) (assembleJ s t w) := by
     apply ((h.sum (readsId.pile ht)).sum ((readsId.pile readsId).pile hv)).cong; filter_upwards with i; simp only [jur,JetS.atK,Pi.add_apply,Pi.mul_apply,smul_eq_mul];ring
lemma take (h:Fitted p): Reads (jur p) (mine p) := Gael.oath (show Gael (jur p) from ⟨_,assent (Gael.oath h.A) (Gael.oath h.B) (Gael.oath h.C)⟩) -- Mine
lemma totals {s t w:Token}(h:Reads (fun i=>(p i).s) s)(hp:Reads (fun i=>(p i).l) t)(ht:Reads (fun i=>(p i).h) w): mine p= assembleJ s t w:= Gael.chooses (assent h hp ht)
protected lemma duty (A:Fitted p)(B:Fitted q): Fitted (p*q):=by
     let a(h:Token):=h.s; exact ⟨Gael.mul A.A B.A,Gael.add (Gael.mul A.A B.B) (Gael.mul A.B B.A),Gael.add (Gael.add (Gael.mul A.A B.C) (Gael.mul A.B B.B)) (Gael.mul A.C B.A)⟩
lemma slopes (h:Fitted p)(hv:Fitted q): mine (p*q)= mine p*mine q:=by
     let S:=trill fun i=>(p i).s; let t:=trill fun i=>(p i).l; let z:=trill fun i=>(p i).h; let y:=trill fun i=>(q i).s; let v:=trill fun i=>(q i).l; let w:=trill fun i=>(q i).h
     have hx:= Gael.oath h.A; have ht:= Gael.oath h.B; have hr:= Gael.oath h.C; have hp:=Gael.oath hv.A; have hL:=Gael.oath hv.B; have hw:=Gael.oath hv.C
     rw [totals hx ht hr, totals hp hL hw, totals (p:=p*q) (hx.pile hp) ((hx.pile hL).sum (ht.pile hp)) (((hx.pile hw).sum (ht.pile hL)).sum (hr.pile hp))]; change assembleJ (S*y) (S*v+t*y) (S*w+t*v+z*y)= assembleJ S t z * assembleJ y v w; apply JetS.eta <;>simp only [assembleJ,ski,JetS.ml_s,JetS.ml_l,JetS.ml_h,JetS.pl_s,JetS.pl_l,JetS.pl_h] <;>ring
lemma verse (u:ℝ→Token)(h:Fitted u)(hv:∀ i,(u i).s=1): mine (fun i=> (u i)⁻¹)=(mine u)⁻¹:=by
     let p:ℝ→Token:=fun i=> (u i)⁻¹; have hp:Fitted p:=by
        let A:= fun i:ℝ=>(u i).l; let B:= fun i:ℝ=>(u i).h; constructor
        · simp only [p,hv,sp_s,inv_one]; exact ⟨_,Reads.constants _⟩
        · have ht: Gael (-A):=⟨_,(Gael.oath h.B).neg⟩; simp only [p,sp_l,hv,one_pow,div_one]; exact ht
        have ht: Gael (A*A-B):=⟨_,(Gael.oath (Gael.mul h.B h.B)).minus (Gael.oath h.C)⟩; simp only [p,sp_h,hv,one_pow,div_one,pow_two,mul_one]; exact ht
     have he:p*u=1:=by funext i; exact JetS.uniting ((hv i).trans_ne one_ne_zero)
     have hx:= slopes hp h; rw [he,show mine (1:ℝ→Token)=1 from Gael.chooses (Reads.selves _)] at hx
     have hz: (mine u).s=1:=by rw [totals (show Reads _ (plainJ 1) from (Reads.constants (1:ℝ)).cong (Filter.Eventually.of_forall hv)) (Gael.oath h.B) (Gael.oath h.C)]; simp [assembleJ,ski]
     change mine p=_; rw [show mine p=mine p*((mine u)⁻¹*mine u) by rw [JetS.uniting (hz.trans_ne one_ne_zero),mul_one],mul_comm (mine u)⁻¹,←mul_assoc,← hx,one_mul]
lemma balance (u q:ℝ→Token)(A:Fitted u)(B:Fitted q)(hp:∀ i,(q i).s=1)(k k':Token)(ha: Reads (jur u) k)(hb:Reads (jur q) k')(h:Fitted fun i=> (q i)⁻¹):Reads (jur (fun i=>u i/q i)) (k/k'):=by
     let p:ℝ→Token:= fun i=>(q i)⁻¹; rw [← (A.take.equality ha), ←(B.take.equality hb),JetS.dv,←verse q B hp,← slopes A h]; exact (Fitted.duty A h).take
variable [FiniteDimensional ℝ E]
lemma arose (u:ℝ→ E)(p:ScriptJ E)(hv:Gael u)(ht:p.B):Fitted fun i=>p (u i):=by obtain ⟨h1,h2,h3⟩:= bondX ht; exact ⟨Gael.climb (E:=E) _ h1 hv,Gael.climb (E:=E) _ h2 hv,Gael.climb (E:=E) _ h3 hv⟩
end Fitted
end Arc
end YM.OPE.Libra
