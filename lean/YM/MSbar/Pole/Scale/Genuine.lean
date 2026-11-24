import YM.MSbar.Pole.Scale.Tear
import YM.MSbar.Pole.Scale.Bronze

/-! # Pole orders of tensor families in all integer testing dimensions

Each operation permits restriction to a smaller ball simultaneously in all arguments.
Laurent subtraction happens on the tensor families before dimension specialization.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

variable {I : Type} [Fintype I] {F G : ℂ → Cloud I}
variable {R r : ℝ}
-- Meromorphic germ equality uniform in dimension and other parameters.
abbrev slit (R:ℝ) := zone R \ {0}

lemma zone_zero (hr:0<R): (0:ℂ) ∈ zone R := (zone_mem ..).mpr (by simpa)
lemma zone_le (hr : r≤R) : zone r ⊆ zone R := Metric.ball_subset_ball hr
lemma neighborhood (hr:0<R) : ∀ᶠ z in nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ,z∈slit R := inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr)) self_mem_nhdsWithin

namespace Ambient.Tensor
omit [Fintype I]
lemma add {F G : Cloud I} (h : Tensor F) (hh : Tensor G) : Tensor (F+G) := by
  constructor
  · intro n J x; simp only [Pi.add_apply]; rw [h.moves,hh.moves]
  intro n x; simp only [Pi.add_apply]; rw [h.agrees,hh.agrees]
lemma sub {F G : Cloud I} (h : Tensor F) (hh : Tensor G) : Tensor (F-G) := by
  constructor
  · intro n J x; simp only [Pi.sub_apply]; rw [h.moves,hh.moves]
  intro n x; simp only [Pi.sub_apply]; rw [h.agrees,hh.agrees]
lemma mul {F G : Cloud I} (h : Tensor F) (hh : Tensor G) : Tensor (F*G) := by
  constructor
  · intro n J x; simp only [Pi.mul_apply]; rw [h.moves,hh.moves]
  intro n x; simp only [Pi.mul_apply]; rw [h.agrees,hh.agrees]
lemma closed {Z : Type*} {t : Filter Z} [t.NeBot] {F : Z → Cloud I} {G : Cloud I} (hf : ∀ᶠ i in t, Tensor (F i))
    (ht : ∀ n x,Tendsto (fun i => F i n x) t (nhds (G n x))) : Tensor G := by
  constructor
  · intro n J x; exact tendsto_nhds_unique_of_eventuallyEq (ht _ _) (ht _ _) (hf.mono fun i hi=>hi.moves n J x)
  intro n x; exact tendsto_nhds_unique_of_eventuallyEq (ht _ _) (ht _ _) (hf.mono fun i hi=>hi.agrees n x)
end Ambient.Tensor
namespace Meridian
variable {U : Set ℂ}
lemma zero : Meridian U (0:ℂ → Cloud I) := ⟨fun _=>Wall.zero,fun _ _ => ⟨fun _ _ _=>rfl,fun _ _=>rfl⟩⟩ -- U implicit
lemma add (h : Meridian U F) (hh : Meridian U G) : Meridian U (F+G):= ⟨fun n => (h.budget n).add (hh.budget n),fun z hz=>(h.tensor z hz).add (hh.tensor z hz)⟩
lemma sub (h : Meridian U F) (hh : Meridian U G) : Meridian U (F-G):= ⟨fun n => (h.budget n).sub (hh.budget n),fun z hz=>(h.tensor z hz).sub (hh.tensor z hz)⟩
lemma mul (h : Meridian U F) (hh : Meridian U G) : Meridian U (F*G):= ⟨fun n => (h.budget n).mul (hh.budget n),fun z hz=>(h.tensor z hz).mul (hh.tensor z hz)⟩
end Meridian

def facets (F:ℂ → Cloud I) (z:ℂ) : Cloud I := fun n => tear (fun z => F z n) z

lemma stress (h : Meridian (zone R) F) (hr:0<R) (n) (x) (z) (hz:z∈zone R) :
    F z n x= F 0 n x+z*facets F z n x:=(h.budget n).unfold_tear hz x

lemma facets_runs (h : Meridian (zone R) F) (hr:0<R): Meridian (zone R) (facets F) := by
  have hh (n): Wall (zone R) (ticket (@id (External I n))) 1 (fun z=> facets F z n) :=
    Wall.torn (show Continuous (fun z:External I n=> 1+‖z‖) from continuous_const.add continuous_norm) (h.budget n)
  have he (z) (hz:z∈slit R) : Tensor (facets F z) := by
    have hp n x := stress h hr n x z hz.1
    have hw := h.tensor z hz.1; have h₁:= h.tensor 0 (zone_zero hr); have ht : z≠0:=hz.2
    constructor
    · intro n J x; apply mul_left_cancel₀ ht
      apply add_left_cancel (a:=F 0 n (J∘x)); rw [← hp,h₁.moves,← hp,hw.moves]
    intro n x; apply mul_left_cancel₀ ht; apply add_left_cancel (a:=F 0 (n+1) (place.pad n ∘ x)); rw [← hp,h₁.agrees,← hp,hw.agrees]
  refine ⟨hh,fun z hz=> ?_⟩
  by_cases hs:z=0
  · subst z
    exact Tensor.closed ((neighborhood hr).mono he) (fun n x=> ((hh n).region 0 hz x).continuousAt.continuousWithinAt)
  exact he z ⟨hz,hs⟩

/-- Unbundled; no canonical radius choice. Fits final existence at all finite demands. -/
def Vortex (k : ℕ) (F : ℂ → Cloud I) : Prop :=
    ∃ (R:ℝ) (G : ℂ → Cloud I), 0<R ∧ Meridian (zone R) G ∧ ∀ z∈slit R, ∀ n x,z^k*F z n x = G z n x

variable {k l : ℕ}
namespace Vortex
lemma mono (h : Vortex k F) (hk : k≤l) : Vortex l F:=by
  obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le hk; subst l
  obtain ⟨R,G,hu,H,h⟩:=h
  refine ⟨R,_,hu,H.weight (b:=fun z=>z^m) (by fun_prop) R (by simp [zone_mem]; intro; intro; linarith), fun z hz n x=>?_⟩
  change _= G z n x*z^m; rw [← h _ hz]; ring
lemma zero (k) : Vortex (I:=I) k 0 := ⟨1,0,zero_lt_one,Meridian.zero,fun _ _ _ _=>by simp⟩
lemma congr (h : Vortex k F) (hr:0<r) (hh:EqOn G F (slit r)): Vortex k G:=by
  obtain ⟨R,P,hp,H,h⟩:=h
  refine ⟨min r R,P,lt_min hr hp,H.mono (zone_le (min_le_right ..)), fun z hz n x=>?_⟩
  have hl : z∈slit r:=⟨zone_le (min_le_left r R) hz.1,hz.2⟩
  rw [hh hl]; exact h z ⟨zone_le (min_le_right r R) hz.1,hz.2⟩ _ _
lemma add (h : Vortex k F) (v : Vortex k G) : Vortex k (F+G) := by
  obtain ⟨R,P,hp,H,h⟩:=h; obtain ⟨S,Q,hq,K,j⟩:=v
  let hs:= zone_le (min_le_left R S); let ht:=zone_le (min_le_right R S)
  refine ⟨min R S,P+Q,lt_min hp hq,(H.mono hs).add (K.mono ht), fun z hz n x=>?_⟩
  simp only [Pi.add_apply,mul_add,h z ⟨hs hz.1,hz.2⟩,j z ⟨ht hz.1,hz.2⟩]
lemma sub (h : Vortex k F) (v : Vortex k G) : Vortex k (F-G) := by
  obtain ⟨R,P,hp,H,h⟩:=h; obtain ⟨S,Q,hq,K,j⟩:=v
  let hs:= zone_le (min_le_left R S); let ht:=zone_le (min_le_right R S)
  refine ⟨min R S,P-Q,lt_min hp hq,(H.mono hs).sub (K.mono ht), fun z hz n x=>?_⟩
  simp only [Pi.sub_apply,mul_sub,h z ⟨hs hz.1,hz.2⟩,j z ⟨ht hz.1,hz.2⟩]
lemma mul (h : Vortex k F) (v : Vortex l G) : Vortex (k+l) (F*G) := by
  obtain ⟨R,P,hp,H,h⟩:=h; obtain ⟨S,Q,hq,K,j⟩:=v
  let hs:= zone_le (min_le_left R S); let ht:=zone_le (min_le_right R S)
  refine ⟨min R S,P*Q,lt_min hp hq,(H.mono hs).mul (K.mono ht), fun z hz n x=>?_⟩
  simp only [Pi.mul_apply]; rw [pow_add,mul_mul_mul_comm,h z ⟨hs hz.1,hz.2⟩,j z ⟨ht hz.1,hz.2⟩]
lemma sum {Z : Type*} (s : Finset Z) (F : Z → ℂ → Cloud I) (h : ∀ z∈s,Vortex k (F z)) : Vortex k (∑ z∈s,F z) := by
  induction s using Finset.induction_on with
  | empty => simpa using zero (I:=I) k
  | @insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun v hv=>h v (Finset.mem_insert_of_mem hv)))
end Vortex
lemma regular_swirl {F:ℂ → Cloud I} (h : Meridian (zone R) F) (hr : 0<R) : Vortex 0 F:=⟨R,F,hr,h,fun _ _ _ _ => by simp⟩
end YM.MSbar.Pole
