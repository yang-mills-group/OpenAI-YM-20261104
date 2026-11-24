import YM.Frontier6.Forest.Twins.Paint

/-!
# A crystal of the deepest band generates a word with two simultaneous
 continuations
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale Flare
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
variable {T: Fareway I} {K:Final C H S}{b a:ℝ}{P:Fabric I}{A B:Art S I}{A' B':ℕ→ Art S I}{x:I→ E4}
attribute [local instance] Spark.ft Spark.de Spark.ne
lemma Flat.bicolor {v:I→ℂ}{u:ℕ→ I→ℂ} (hv: Flat T (fun d i=> v i-u d i))(hh:T.Costs v a): Bicolor T v u:= ⟨⟨_,hh⟩,hv⟩
lemma Flat.mapped {X Y 𝕜: Type*}[NontriviallyNormedField 𝕜][SeminormedAddCommGroup X][SeminormedAddCommGroup Y][NormedSpace 𝕜 X][NormedSpace 𝕜 Y]{u:ℕ→ I→ X}(h: Flat T u)(L:X →L[𝕜] Y): Flat T (fun d i=> L (u d i)):=fun a=>(h a).mono fun d hd=> hd.mapped L
lemma Flat.cf {X:Type*}[SeminormedAddCommGroup X]{u v:ℕ→ I→ X}(h: Flat T u)(he:∀ᶠ d in atTop, u d=ᶠ[T.via] v d): Flat T v:= fun a=> ((h a).and he).mono fun i hi=> hi.1.cf hi.2
lemma Bicolor.rfl {u:I→ ℂ}(h:T.Costs u a): Bicolor T u (fun _=>u):= ⟨⟨a,h⟩,fun a=> Eventually.of_forall fun _=> Fareway.Costs.free.cf (Eventually.of_forall fun _=>by simp)⟩
namespace Prism
lemma single_light (A:Spark S I)(h:A.Shine T b P): Prism K T b P A.real (A.almost K):=by
    let F(_:Unit):= A; have he: Wide T (home F) (b-1):=fun _ _ hz=> (hz rfl).elim
    have hx: showAt F=A.real:=by ext1 i; unfold showAt; rw [Fintype.prod_unique]
    have hk:shared K F=A.almost K:=by ext1 d;ext1 i; unfold shared; rw [Fintype.prod_unique]
    exact hk ▸ hx ▸ battery (fun _=> h) (sub_one_lt _) he -- defeq F not above rewrite?
lemma step (v:S.Tag)(hx:Contains T P x): Prism K T b P (fun i=>letter S (x i) v) (fun _ i=> letter S (x i) v):=by
   let A:= Spark.lone x v; have he:= Spark.real_lone x v; have hr:= single_light (K:=K) A (Spark.shines_lone (b:=b) v hx); refine hr.congruence (Agrees.cf (Filter.EventuallyEq.of_eq he)) ?_
   refine (eventually_ge_atTop v.fst).mono fun d hd=>?_ ; refine Eventually.of_forall fun i=>?_ ; unfold Spark.almost A; rw [he]; exact letter_all K d _ v.snd hd
lemma neg (h:Prism K T b P A A') : Prism K T b P (-A) (-A'):=by
   refine (h.scale (Bicolor.rfl (Fareway.Costs.const (-1:ℂ)))).cf (Eventually.of_forall fun _=> neg_one_smul ..) (Eventually.of_forall fun _=> Eventually.of_forall fun _=> neg_one_smul ..)
lemma sub (h:Prism K T b P A A')(he:Prism K T b P B B'): Prism K T b P (A-B) (A'-B'):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add he.neg
lemma folds {V:Type*} (s:Finset V){A:V→Art S I}{A':V→ℕ→ Art S I}(h:∀ i∈s, Prism K T b P (A i) (A' i)): Prism K T b P (fun i=>∑ j∈s,A j i) (fun d i=>∑ j∈s,A' j d i):=by
   induction s using Finset.induction_on with
   | empty=> simp_rw [Finset.sum_empty]; exact zero
   | @insert i s he ih=> simp_rw [Finset.sum_insert he]; exact (h _ (mem_insert_self ..)).add (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma hue (d:ℕ){v:I→ S.Field d}{v':ℕ→ I→ S.Field d}(hx:Contains T P x)(he:T.Costs v a) (hp: Flat T (fun d i=> v i-v' d i)): Prism K T b P (fun i=>suit K (x i) d (v i)) (fun w i=>suit K (x i) d (v' w i)):=by
   simp_rw [suit_eq]; apply folds; intro i _; let V:= LinearMap.toContinuousLinearMap ((marker K d).coord i ∘ₗ face K d)
   have hh:= hp.mapped V; simp_rw [map_sub] at hh; exact (step ⟨d,(marker K d i).val⟩ hx).scale (hh.bicolor (he.mapped V))
lemma full (hA:Mist T b P A a)(he:Local T P x b)(hv:0<b)(hx:Contains T P x): Prism K T b P A (fun d i=> all K (x i) d (A i)):=by
   have hz(w:ℕ):= he.ready K hv w
   induction hA with
   | @word V _ _ _ c v hP h =>
      let U : Spark S I := { Part:=V, whereAt:=c, origin:=x, tags:=v }; have hy : U.Shine T b P := {level:=hP, lights:=fun i=> he.cost (h.contains (contains_sheet c i)), supports:=h, lives:=hx}; exact single_light U hy
   | add h g ih jh=>
      apply (ih.add jh).cf Filter.EventuallyEq.rfl; apply Eventually.of_forall; intro d; filter_upwards [lights K d (hz d) h.acts, lights K d (hz d) g.acts] with i hi hg; exact (all_plus K _ _ _ hi hg).symm
   | scale h g ih=>
      refine (ih.scale (Bicolor.rfl h)).cf Filter.EventuallyEq.rfl (Eventually.of_forall fun d=>?_); exact (lights K d (hz d) g.acts).mono fun i hi=>(all_scal K _ _ _ _ hi).symm
   | cf h hk ih=>
      refine ih.cf hk (Eventually.of_forall fun _=>?_); exact hk.mono fun i hi=> congr_arg _ hi
   | mono h hp ih=> exact ih
   | zero z=>
      apply zero.cf Filter.EventuallyEq.rfl; refine Eventually.of_forall fun d=> Eventually.of_forall fun i=>(all_void ..).symm
end Prism
end YM.Frontier6.Forest
