import YM.RG3.Alpes.Claris
/-!
# Footprints of every external test/address **separately** at every term

 Dread clients give T s spaces normed with all requested derivatives baked
 in their unit tests & dilation controls. Keep G field dependencies exact via
 Regular/Attaches/Logo.Lanes. Here trade only address documents, preserving
 every question answered (functional equality on test germ or theta domain).
 `houses` pins finite support *of each query* and tests may have infinite
 census e.g all point-evals plus distributions. Require formulas to register
 equality whenever tests agreeing on those QUERIES wholly covered by shown
 S. This encodes even continuum addresses and ordered derivative probes not
 limited to marking ONE position. For actual addresses outside smallest torus
 chart use all lifted supports OR keep this periodic footprint plus customers'
 weighted polynomial test norm & exponent reserves (any consumer needing
 exponential lifted path retains extra ticket until charge before discarding).
 Accounting requires exterior polynomial holder norm on T, not transport
 of analytic kernels in continuum WilsonX graphs with stronger exponential
 address-measure cost (that fee still upstream!). Can include address tests
 wholly inside ancestor cells with carrier one marked site if that's actual
 Fk/Γ reader. Long address measure presentations should use shell-paid,
 retained path supports and actual norm widths, do not aggregate & then
 infer that support price.Gauge labels & correlations costs independently
 across power streams. H budgets.Retention uses dual notion not changing
 the physical mask area.Chapel.Asset. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Alpes
open Function Filter Lattice RG Wilson Marker RG3.Held Finset
open scoped Topology BigOperators Classical
variable {V : Type*}[DecidableEq V]{T:V→Type*}[∀ i,NormedAddCommGroup (T i)][∀ i, NormedSpace ℝ (T i)]
variable {n:Side}
/-- Domain-specific support of all queries to T tests (incl ordered
 derivatives and coefficient indices as declared separately by compiler on this
 clock). Numerical support travel stamped at their TRUE expense. Universe of
 query/value can be encoded in Type by images; no claim for infinite Wing,
 `T : Type*` supports many variants.Built-in unit tests only but Outlook on ALL z,
 not conditionally priced dependence. -/
structure Vine (n:Side)(T:V→Type*) where
    key:V→Type
    house: (v:V)→key v→ Support n
    reports(v:V)(k:key v):Type
    say(v:V)(k:key v): T v→ reports v k

namespace Vine
variable (b:Vine n T)
def hush (s:Finset V)(U:Support n)(x y:(i:V)→T i) := ∀ i∈s,∀ h:b.key i,b.house i h⊆U→ b.say i h (x i)=b.say i h (y i)
omit [DecidableEq V] [∀ i, NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)] in
lemma fixed (s:Finset V)(U:Support n)(x y:(i:V)→T i)(h:∀ i∈s,x i=y i): b.hush s U x y:=fun i hi _ _=>congrArg _ (h i hi)
omit [DecidableEq V] [∀ i, NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)] in
lemma mono {s t:Finset V}{U A:Support n}{x y:(i:V)→T i}(h:b.hush t A x y)(hs:s⊆t)(hU:U⊆A):b.hush s U x y:=fun i hi j hx=>h i (hs hi) j (Finset.Subset.trans hx hU)
-- avoid implicit answer only unit: harmony on ALL vectors test space
structure Rune {E : Type*}[AddCommGroup E][Module ℝ E](s:Finset V)(A:Support n)(f:Dais T→E):Prop where
   plays : Tone T s f
   stays x y : b.hush s A x y → Tone.core T s f x = Tone.core T s f y
namespace Rune
variable {E:Type*}[AddCommGroup E][Module ℝ E]{s t : Finset V}{A A':Support n}{f g:Dais T→E}
lemma still : b.Rune s A (0:Dais T→E):=⟨Tone.still,fun _ _ _=>by simp [Tone.core]⟩
lemma const (q:E): b.Rune ∅ A fun _=>q:=⟨Tone.pure q,fun _ _ _=>by simp [Tone.core]⟩
variable {b}
lemma remit (h:b.Rune s A f)(hh:b.Rune s A g): b.Rune s A (f+g):=by
    refine ⟨h.plays.adds hh.plays,fun x y hi=>?_⟩
    calc
      _ = Tone.core T s f x+Tone.core T s g x:=by simp [Tone.core,smul_add]
      _ = _ := by rw [h.stays x y hi, hh.stays x y hi]; simp [Tone.core,smul_add]
lemma neg (h:b.Rune s A f): b.Rune s A (-f):=by
    refine ⟨h.plays.neg,fun x y hi=>?_⟩
    unfold Tone.core; simp only [Pi.neg_apply,smul_neg]; exact congrArg Neg.neg (h.stays x y hi)
lemma sub (h:b.Rune s A f)(hh:b.Rune s A g): b.Rune s A (f-g):= sub_eq_add_neg f g ▸ h.remit hh.neg
lemma soar (h:b.Rune s A f)(hA:A⊆A'): b.Rune s A' f:=⟨h.plays,fun x y hh=>h.stays x y (b.mono hh (Finset.Subset.refl _) hA)⟩
lemma emit {F:Type*}[AddCommGroup F][Module ℝ F](h:b.Rune s A f)(φ:E→ₗ[ℝ]F): b.Rune s A (fun x=>φ (f x)):=by
    refine ⟨h.plays.emit φ,fun x y hh=>?_⟩; unfold Tone.core; rw [← φ.map_smul, ← φ.map_smul]; exact congrArg φ (h.stays x y hh)
lemma bind {f g:Dais T→ℂ}(h:b.Rune s A f)(ht:b.Rune t A g)(hp:Disjoint s t): b.Rune (s∪t) A (f*g):=by
    refine ⟨h.plays.bind ht.plays hp,fun x y hh=>?_⟩
    have he(x): Tone.core T (s∪t) (f*g) x=Tone.core T s f x *Tone.core T t g x:=by
        simp [Tone.core,prod_union hp,Complex.real_smul]; ring
    rw [he,he,h.stays _ _ (b.mono hh subset_union_left (Finset.Subset.refl _)), ht.stays _ _ (b.mono hh subset_union_right (Finset.Subset.refl _))]
lemma total {ι}(q:Finset ι)(g:ι→Dais T→E)(he:∀ i∈q,b.Rune s A (g i)): b.Rune s A (fun x=>∑ i∈q,g i x):=by
    induction q using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact still _
    | insert i l h ih=>simp only [sum_insert h]; exact (he i (mem_insert_self ..)).remit (ih (fun t ht=> he t (mem_insert_of_mem ht)))
lemma assembly {ι}(f:ι→Dais T→ℂ)(h:∀ i,b.Rune s A (f i))(he:∀x,Summable (fun i=>f i x)): b.Rune s A (fun x=>∑' i,f i x):=by
    refine ⟨Tone.assembly f (fun i=>(h i).plays) he,fun x y hh=>?_⟩
    simp only [Tone.core,←(he _).tsum_const_smul] -- wrong direction
    exact tsum_congr fun i=> (h i).stays _ _ hh
lemma funct {F:Type*}[AddCommGroup F][Module ℝ F](h:b.Rune s A f){D:Set E}
    (hx:∀x,f x∈D)(hr:∀x:E,x∈D→∀r:ℝ,r•x∈D)(φ:E→F)(ad:∀x y:E,x∈D→y∈D→φ (x+y)=φ x+φ y)(se:∀x:E,x∈D→∀r:ℝ,φ (r•x)=r•φ x): b.Rune s A (fun i=>φ (f i)):=by
    refine ⟨Tone.functor h.plays hx hr φ ad se, fun x y hh=>?_⟩
    simp only [Tone.core]; rw [← se _ (hx _),← se _ (hx _)]; exact congrArg φ (h.stays _ _ hh)
lemma pi {ι:Type*}{Y:ι→Type*}[∀ i,AddCommGroup (Y i)][∀i,Module ℝ (Y i)]{f:Dais T→(i:ι)→Y i} (h:∀ i,b.Rune s A fun x=>f x i) : b.Rune s A f:=⟨Tone.pi (fun i=>(h i).plays),fun _ _ hh=>funext (fun i=> (h i).stays _ _ hh)⟩
lemma read {ι:Type*}{Y:ι→Type*}[∀ i,AddCommGroup (Y i)][∀i,Module ℝ (Y i)]{f:Dais T→(i:ι)→Y i} (h:b.Rune s A f)(i:ι): b.Rune s A fun x=>f x i:=h.emit (LinearMap.proj i)
lemma cscale {f:Dais T→ℂ}(h:b.Rune s A f)(x:ℂ): b.Rune s A fun i=>x*f i:= h.emit (Algebra.lmul ℝ ℂ x)
end Rune
end Vine
end YM.RG3.Alpes
