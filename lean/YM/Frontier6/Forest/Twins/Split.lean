import YM.Frontier6.Forest.Render.Flask

/-! Matched pairs of offerings at one band. Closed under disjoint multiplication
 (centers and footprints) but estimates not abstract: the generative case has
 all its choices in the shared exact theory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
-- `Congr` doesn't assert legit local usage. additional hypotheses supplied there
abbrev Agrees (T:Fareway I)(K:Final C H S)(A B:Art S I):Prop:= ∀ᶠ i in T.via,Tale.Congr K (A i) (B i)
-- scalar flatness for each arbitrary valuation (not flat in coupling)
def Flat (T:Fareway I){X:Type*}[SeminormedAddCommGroup X](A:ℕ→ I→ X): Prop:= ∀ w:ℝ,∀ᶠ d:ℕ in atTop, T.Costs (A d) w
structure Bicolor (T:Fareway I)(A:I→ℂ)(B:ℕ→ I→ℂ): Prop where
    color : ∃ u,T.Costs A u
    change : Flat T (fun d=> A-B d)
open Flare
attribute [local instance] Spark.ft Spark.de Spark.ne
inductive Prism (K:Final C H S)(T:Fareway I)(b:ℝ)(P:Fabric I): Art S I → (ℕ → Art S I)→ Prop where
| battery {V:Type}[Fintype V][DecidableEq V]{F:V→Spark S I}(h:∀ v,(F v).Shine T b P){a:ℝ}(he:a<b)(hk:Wide T (home F) a): Prism K T b P (showAt F) (shared K F)
| add {A B A' B'}(h:Prism K T b P A A')(he:Prism K T b P B B'): Prism K T b P (A+B) (A'+B')
| scale {A A' u u'}(h: Bicolor T u u')(he:Prism K T b P A A'): Prism K T b P (fun i=> u i • A i) (fun d i=>u' d i • A' d i)
| congruence {A B A' B'} (h:Prism K T b P A A')(he:Agrees T K A B)(hv:∀ᶠ d in atTop, Agrees T K (A' d) (B' d)): Prism K T b P B B'
| zero : Prism K T b P 0 0
variable {T: Fareway I}{b a:ℝ}{P Q:Fabric I}{K:Final C H S}{A B:Art S I}{A' B':ℕ→ Art S I}
lemma Agrees.symm (h:Agrees T K A B): Agrees T K B A:= h.mono fun i hi=> hi.symm K
lemma Agrees.cf (h:A=ᶠ[T.via] B): Agrees T K A B:= h.mono fun i hi=> (by rw [hi]; exact Tale.almost K _)
lemma Agrees.rfl (A:Art S I) : Agrees T K A A:= Eventually.of_forall fun _=> Tale.almost K _
lemma Agrees.mul (h:Agrees T K A B){C D:Art S I}(he:Agrees T K C D): Agrees T K (A*C) (B*D):= (h.and he).mono fun _ hi=> hi.1.mul K hi.2
namespace Prism
variable (h:Prism K T b P A A')
include h
lemma cf (he:A=ᶠ[T.via] B)(hv:∀ᶠ d in atTop, A' d=ᶠ[T.via] B' d) : Prism K T b P B B':= h.congruence (Agrees.cf he) (hv.mono fun i hi=> Agrees.cf hi)
lemma broad (he:Extends T Q P): Prism K T b Q A A':=by
    induction h with
    | battery v he' h' => exact battery (fun i=> (v i).extends he) he' h'
    | add _ _ ih jh=> exact ih.add jh
    | scale a _ ih=> exact ih.scale a
    | congruence h hk hv ih=> exact ih.congruence hk hv
    | zero=> exact zero
lemma mul (h':Prism K T b Q B B')(he:Cross T P Q a)(ha:a<b) : Prism K T b (P⊔Q) (A*B) (A'*B'):=by
   induction h with
   | @battery V _ _ F hf v hv hw=>
      induction h' with
      | @battery X _ _ F' hF u hu hh=>
         let a':= max a (max v u); have ha':a'<b:= max_lt ha (max_lt hv hu)
         have hp:= homes_join F F' hf hF (hw.higher (b:=a') (le_trans (le_max_left ..) (le_max_right ..))) (hh.higher (le_trans (le_max_right ..) (le_max_right ..))) (he.scale (le_max_left ..))
         apply (battery (shine_joint F F' hf hF) ha' hp).cf (Filter.EventuallyEq.of_eq (showAt_join F F')); exact Eventually.of_forall fun d=> Filter.EventuallyEq.of_eq (shared_join K F F' d)
      | add _ _ ih jh=> rw [mul_add,mul_add]; exact ih.add jh
      | @scale X X' u u' hh hv ih=>
         exact (ih.scale hh).cf (Eventually.of_forall fun i=>(mul_smul_comm ..).symm) (Eventually.of_forall fun d=>Eventually.of_forall fun i=>(mul_smul_comm ..).symm)
      | congruence h he hv ih=> exact ih.congruence (Agrees.mul (Agrees.rfl _) he) (hv.mono fun d hd=>Agrees.mul (Agrees.rfl _) hd)
      | zero=> rw [mul_zero,mul_zero]; exact zero
   | add _ _ ih jh=> rw [add_mul,add_mul]; exact ih.add jh
   | @scale A A' u u' hh' hv' ih=>
      exact (ih.scale hh').cf (Eventually.of_forall fun i=>(smul_mul_assoc ..).symm) (Eventually.of_forall fun d=>Eventually.of_forall fun i=>(smul_mul_assoc ..).symm)
   | congruence h he hv ih=>exact ih.congruence (Agrees.mul he (Agrees.rfl _)) (hv.mono fun d hd=>Agrees.mul hd (Agrees.rfl _))
   | zero=> rw [zero_mul,zero_mul]; exact zero
end Prism
end YM.Frontier6.Forest
