import YM.RG3.Alpes.Flower
/-!
# Extend and even derivative maps preserve relationship
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Alpes
open Function Filter Lattice RG Wilson Marker RG3.Held Finset
open scoped Topology BigOperators Classical ContDiff
variable {V : Type*}[DecidableEq V](T:V→Type*)[∀ i, NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)]
variable {E:Type*}[AddCommGroup E][Module ℝ E]
namespace Tone
variable (s:Finset V)
-- Beam extension.Cases index from unit shading not all edges needed. -/
def core (f:Dais T→E)(x:(i:V)→T i):E:=(∏ i∈s,beam T x i) • f (paint T x)
omit [DecidableEq V][(i:V)→ NormedSpace ℝ (T i)] in
lemma beam_unit(x:Dais T)(i:V):beam T (shades T x) i=1:=max_eq_left (x i).2
omit [DecidableEq V] in
lemma bleached(x:Dais T) : paint T (shades T x)=x:=by funext i; apply Subtype.ext; change (beam T _ i)⁻¹ • _ = _; rw [beam_unit,inv_one,one_smul];rfl
omit [DecidableEq V] in
lemma cast (f:Dais T→E)(x:Dais T):core T s f (shades T x)=f x:=by unfold core; simp_rw [beam_unit,prod_const_one,bleached,one_smul]
variable {T s}
lemma admits {f:((i:V)→T i)→E}(h:Letter ℝ T s f): f=core T s (fun x=> f (shades T x)):=funext (shaded f h)
lemma rider {f:Dais T→E}(h:Tone T s f):Letter ℝ T s (core T s f):= by
   obtain ⟨g,hg,he⟩:=h; rw [show f=_ from funext he, ← admits hg]; exact hg -- via admits he funext
lemma ordinary {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{f:Dais T→F}(h:Tone T s f){r:ℝ}(hh:∀ x,‖f x‖≤r):∀ z:(i:V)→T i, ‖core T s f z‖≤(∏ i∈s,‖z i‖)*r:=signal_norm (rider h) (fun i=>by rw [cast]; exact hh i)

/-- Natural transform on a DOMAIN of a linear map only (e.g. Π calibration
 or field derivatives on Regular). No arbitrary extension to a linear
 operator on all torus functions needed. -/
lemma functor {F:Type*}[AddCommGroup F][Module ℝ F]{f:Dais T→E}(h:Tone T s f)
    {D:Set E}(hx:∀x,f x∈D)(hr:∀x:E,x∈D→∀r:ℝ,r•x∈D)(φ:E→F)(ad:∀x y:E,x∈D→y∈D→φ (x+y)=φ x+φ y)
    (se:∀x:E,x∈D→∀r:ℝ,φ (r•x)=r•φ x): Tone T s (fun x=>φ (f x)) :=by
  let u:=core T s f; let v x:=φ (u x)
  have ht(x):(u x)∈D:= hr _ (hx _) _
  let H:= h.rider
  refine ⟨v,⟨fun x y hh=>congrArg φ (H.stay _ _ hh),?_,?_⟩,fun x=>?_⟩
  · intro x i hi a b; unfold v; rw [show u (update x i (a+b)) =_ from H.join x i hi a b,ad _ _ (ht _) (ht _)]
  · intro x i hi z a; unfold v; rw [show u (update x i (z • a)) =_ from H.scale x i hi z _,se _ (ht _)]
  exact congrArg φ (cast _ _ _ _).symm
-- evaluate globally.Encode points stencil tests.
lemma pi {ι:Type*}{Y:ι→Type*}[∀ i,AddCommGroup (Y i)][∀i,Module ℝ (Y i)]{f:Dais T→(i:ι)→Y i}(h:∀ i,Tone T s fun z=> f z i): Tone T s f:=by
   choose g hg he using h
   refine ⟨fun z i=>g i z,?_ ,fun u=>funext (fun i=>he i u)⟩
   exact ⟨fun _ _ hh=>funext (fun i=> (hg i).stay _ _ hh), fun _ _ hi a b=>funext (fun i=> (hg i).join _ _ hi a b),fun _ _ hi r a=> funext (fun i=> (hg i).scale _ _ hi _ _)⟩
lemma at_key {ι:Type*}{Y:ι→Type*}[∀ i,AddCommGroup (Y i)][∀i,Module ℝ (Y i)]{f:Dais T→(i:ι)→Y i}(h:Tone T s f)(i:ι): Tone T s fun z=> f z i:= h.emit (LinearMap.proj i)
end Tone
end YM.RG3.Alpes
