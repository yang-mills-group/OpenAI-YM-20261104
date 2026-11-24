import YM.RG3.Held.Typed
/-!
# Restricted test families with every normalized derivative query.A.User

At one fixed clock/mark layout, not test locations modulo translation.
Declared vector test spaces over real incl reflection (extension to complex
when no conjugated receipts desired straightforward w/ .Held). Needn't
be complete, but must norm every used derivative at their true location
(including weighted-polynomial test budgets, stencil vectors, pulls & offsets
as needed, do not identify different positions on torus without proving
retention vs addressing interface). Prove transformation on UNIT tests,
recover genuine multilinearity and every mixed norm by actual lift. This
avoids assuming pricing summability over an unbounded Θ before using mergers!
Only price on yard Υ. No positive test count or Banach equivalence constants.
Multilinear transport operator.For nonwrapping primary joint extraction this
 version will extract a vector *on EVERY test*, including test polynomials,
 not contracting the resulting section-valued-in-tests collection through
 one mark WITHOUT converting to joint finite weight basis; use other consumers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Alpes
open Function Filter Lattice RG Wilson Marker RG3.Held Finset
open scoped Topology BigOperators Classical
variable {V : Type*}[DecidableEq V](T:V→Type*)[∀ i, NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)]
abbrev Admiral (i:V) := { z:T i//‖z‖≤1 }
abbrev Dais (T:V→Type*)[∀ i,NormedAddCommGroup (T i)]:= (i:V)→ { z:T i//‖z‖≤1 }
-- not relying bounded space coerces
instance nonemptyOf(i:V):Inhabited (Admiral T i):=⟨⟨0,by simp⟩⟩

def shades (z:Dais T) (i:V):T i:= (z i).val
private def band (z:(i:V)→T i)(hz:unit T z):Dais T:=fun i=>⟨z i,hz i⟩
variable {E:Type*}[AddCommGroup E][Module ℝ E](s:Finset V)
/-- A function on **restricted** tests that really is multilinear outside
 and carries chosen witness. No assumed topological dual identification;
 `.shade` obtains norm for typed test spaces solely from the actual Book.ISearch.
 -/
def Tone (f:Dais T→ E):Prop:=∃ g:((i:V)→T i)→E,Letter ℝ T s g∧∀ x,f x=g (shades T x)
namespace Tone
variable {T s}{f g:Dais T → E}
lemma still : Tone T s (0:Dais T → E):= ⟨0,Letter.still,fun _=>rfl⟩
lemma pure (q : E) : Tone T ∅ fun _=>q :=⟨fun _=>q,Letter.const _,fun _=>rfl⟩
lemma adds (h:Tone T s f)(h':Tone T s g):Tone T s (f+g):=by
   obtain ⟨u,hU,hu⟩:=h; obtain ⟨v,hV,hv⟩:=h'; refine ⟨u+v,hU.add hV,fun i=>?_⟩; simp only [Pi.add_apply,hu,hv]
lemma neg (h:Tone T s f):Tone T s (-f):=by
   obtain ⟨u,hU,hu⟩:=h; refine ⟨-u,hU.neg,fun i=>?_⟩; simp only [Pi.neg_apply,hu]
lemma sub (h:Tone T s f)(h':Tone T s g):Tone T s (f-g):=by rw [sub_eq_add_neg]; exact h.adds h'.neg
lemma emit {F:Type*}[AddCommGroup F][Module ℝ F](h:Tone T s f)(φ:E→ₗ[ℝ]F): Tone T s (φ ∘ f):= by
   obtain ⟨u,hU,hu⟩:=h; exact ⟨φ∘u,hU.linear _,fun i=> congrArg φ (hu i)⟩
lemma stay (h:Tone T s f)(i j)(he:∀ v∈s,i v=j v): f i=f j:=by
   obtain ⟨u,hU,hu⟩:=h; rw [hu,hu]; exact hU.stay _ _ (fun a ha=>congrArg (fun x:Admiral T a=>x.val) (he a ha))
-- product no test re-use. algebra for costs.
lemma bind {f g:Dais T→ℂ}{t : Finset V}(h:Tone T s f)(h':Tone T t g)(hh:Disjoint s t): Tone T (s∪t) (f*g):=by
   obtain ⟨u,hU,hu⟩:=h; obtain ⟨v,hV,hv⟩:=h'; refine ⟨u*v,hU.bind hV hh,fun i=> ?_⟩; simp only [Pi.mul_apply,hu,hv]
lemma rscale (h:Tone T s f)(r:ℝ):Tone T s (fun x=>r • f x):= h.emit (r • LinearMap.id (R:=ℝ) (M:=E)) -- check
lemma multiply (q:ℂ){f:Dais T→ℂ}(h:Tone T s f): Tone T s (fun x=>q*f x):=h.emit (Algebra.lmul ℝ ℂ q)
lemma total {ι}(q:Finset ι)(f:ι→Dais T→E)(he:∀ i∈q,Tone T s (f i)):Tone T s (fun x=>∑ i∈q,f i x):=by
    induction q using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact still
    | insert i l hh ih=>simp only [sum_insert hh]; exact (he _ (mem_insert_self ..)).adds (ih (fun v hv=>he v (mem_insert_of_mem hv)))
-- uniqueness exterior & summability. explicit normalize >1 avoids small reciprocals.
variable (T)
def beam (x:(i:V)→T i)(i:V):ℝ:=max 1 ‖x i‖
omit [DecidableEq V][(i:V)→NormedSpace ℝ (T i)] in
lemma beam_ge (x:(i:V)→T i)(i:V):1≤beam T x i:=le_max_left ..
def paint (x:(i:V)→T i):Dais T:=fun i=> ⟨(beam T x i)⁻¹ • x i, by
    have hp:=zero_lt_one.trans_le (beam_ge T x i)
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact (mul_le_mul_of_nonneg_left (le_max_right 1 _) (inv_nonneg.mpr hp.le)).trans (by rw [← show beam T x i=max 1 ‖x i‖ from rfl,inv_mul_cancel₀ hp.ne'])⟩
variable {T}
lemma shaded (f:((i:V)→T i)→E)(h:Letter ℝ T s f)(x): f x=(∏ i∈s,beam T x i) • f (shades T (paint T x)):=by
    let g(i:V):=beam T x i
    let y(t:Finset V):=(fun i=> if i∈t then (shades T (paint T x) i) else x i)
    have he(t:Finset V)(ht:t⊆s): f x=(∏ i∈t,g i) • f (y t):= by
        induction t using Finset.induction_on with
        | empty=> simp [y]
        | insert i k hx ih=>
          rw [ih (insert_subset_iff.mp ht).2, prod_insert hx, mul_comm (g i), mul_smul]
          congr 1
          have hh: y (insert i k)=update (y k) i ((g i)⁻¹ • x i):= by
            funext j; by_cases hj:j=i
            · subst j; simp [y,paint,shades,g]
            simp [hj,update_of_ne, y]
          rw [hh,h.scale _ i (ht (mem_insert_self ..))]
          have hh': update (y k) i (x i) = y k:= by rw [← show y k i=x i from if_neg hx,update_eq_self]
          have hl:0<g i:=zero_lt_one.trans_le (beam_ge T x _)
          rw [hh', smul_smul, mul_inv_cancel₀ hl.ne',one_smul]
    rw [he s (Subset.refl _) ,h.stay (y s) (shades T (paint T x)) (fun i hi=>?_)]
    exact if_pos hi
lemma assembly {ι}(f:ι→Dais T→ℂ)(h:∀ i,Tone T s (f i))(hh:∀ x,Summable (fun i=>f i x)): Tone T s (fun x=>∑' i,f i x):=by
    choose F hF hX using h
    have hG(x:(i:V)→T i):Summable (fun i=> F i x):=by
      have hp i:=shaded (F i) (hF i) x
      simp_rw [hp,← hX]; exact (hh _).const_smul _
    refine ⟨_,Letter.assembly F hF hG,fun x=>?_⟩; simp_rw [hX]
lemma signal_norm {U:Type*}[NormedAddCommGroup U][NormedSpace ℝ U]{g:((i:V)→T i)→U}(h:Letter ℝ T s g){r:ℝ}(hh:∀ x:Dais T,‖g (shades T x)‖≤r)(x): ‖g x‖≤(∏ i∈s,‖x i‖)*r:=
    h.cost x (fun y hy=>hh (band T y hy))

end Tone
end YM.RG3.Alpes
