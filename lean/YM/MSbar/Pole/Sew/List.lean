import YM.MSbar.Pole.Sew.Stitch

/-!
# Counting integrations in an amplitude

Finite list of meromorphic tensors with marker `l` counting actual dimension-dependent
momentum integrations in this calculation. It may be smaller than the loop order because
of local counterterms. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Sew Thread Symbol
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]

/-- Atom of one homogeneity type for positive regularizing length, fixed engineering
scale read from graph's external weights. -/
structure Piece (I : Type) where
  l : ℕ
  g : ℂ → Cloud I

namespace Piece
variable {U V M : Finset I} {a:ℤ}

def sum (s : List (Piece I)) (M:Finset I) (a:ℤ) (r:ℝ) : ℂ → Cloud I := (s.map (fun x=>roll M ⟨a,x.l⟩ r x.g)).sum
-- no-loop condition involves physical value along actual positive length
structure Single (p : Piece I) (M:Finset I) (a :ℤ)(U V: Finset I) : Prop where
  swirl : ∃ k,Vortex k p.g
  shape : Acts U V p.g
  tree : p.l=0 → rests M a p.g
-- coherent at all positive r
structure Stack (s : List (Piece I)) (M:Finset I) (a:ℤ)(U V:Finset I) : Prop where
  graded : ∀ x∈s,Single x M a U V
  combined : ∀ r:ℝ,0<r → Vortex 0 (sum s M a r)
-- after cutting the last scale
structure Flag (s : List (Piece I)) (M : Finset I)(a:ℤ)(U V:Finset I) : Prop where
  law (x) (hx : x∈s) : (∃ k,Vortex k x.g) ∧ Acts U V x.g ∧ Wing M ⟨a,x.l⟩ x.g
  clean : ∀ r:ℝ,0<r→ Vortex 0 (sum s M a r)

@[simp] lemma sum_nil (M:Finset I)(a:ℤ)(r:ℝ): sum [] M a r=0:=rfl
@[simp] lemma sum_cons (p:Piece I)(s:List (Piece I))(M:Finset I)(a:ℤ)(r:ℝ): sum (p::s) M a r=roll M ⟨a,p.l⟩ r p.g+sum s M a r:=rfl
@[simp] lemma sum_cat (s t:List (Piece I))(M:Finset I)(a:ℤ)(r:ℝ): sum (s++t) M a r=sum s M a r+sum t M a r:=by simp [sum]

-- Rows with no flow (including unpaired singletons)
lemma native (H: Cloud I) (h:Local M a H) (hp:Shape U V H): Stack [⟨0,fun _=>H⟩] M a U V:= by
  constructor
  · intro x hx; simp only [List.mem_singleton] at hx; subst x
    exact ⟨⟨0,regular_swirl h.regular.constant zero_lt_one⟩,Eventually.of_forall fun _=> hp,fun _=> Eventually.of_forall fun z n x=>
      ⟨_,(tendsto_const_nhds (x:=H n x)).congr' (by filter_upwards [self_mem_nhdsWithin] with t ht; exact (h.echo t ht z n x).symm)⟩⟩
  intro r hr; simp_rw [sum_cons,sum_nil,add_zero]; exact roll_vortex _ _ (regular_swirl h.regular.constant zero_lt_one) hr

lemma Stack.raises {s: List (Piece I)} (h:Stack s M a U V) {U' V'} (hh:U ⊆ U') (hp:V' ⊆ V) : Stack s M a U' V' := by
  refine ⟨fun x hx=>?_,h.combined⟩
  obtain ⟨hV,hS,hT⟩:=h.graded x hx; exact ⟨hV,(show ∀ᶠ z in approaching,_ from hS).mono (fun z (hv:Shape U V (x.g z))=> ⟨fun n x y ha=>hv.sees n x y fun i hi=> ha i (hh hi), fun i hi=> hv.angle i (hp hi)⟩),hT⟩

lemma Flag.zero : Flag ([]:List (Piece I)) M a U V:=⟨fun x hx=>by simp at hx,fun _ _=>Vortex.zero _⟩
lemma Flag.add {s t:List (Piece I)} (h:Flag s M a U V)(p:Flag t M a U V): Flag (s++t) M a U V:=⟨fun i hi=> (List.mem_append.mp hi).elim (fun he=>h.law i he) (fun he=>p.law i he),fun r hr=>by rw [sum_cat]; exact (h.clean r hr).add (p.clean r hr)⟩
variable {T:Thread I} {Y : Finset I}
lemma rough {s:List (Piece I)} (h : ∀ x∈s, ∃ k, Vortex k x.g) (M:Finset I) (a:ℤ) (r:ℝ) (hr:0<r) : ∃ k,Vortex k (sum s M a r) := by
  induction s with
  | nil=> exact ⟨_,Vortex.zero 0⟩
  | cons i s ih=>
    obtain ⟨k,hk⟩:=h i List.mem_cons_self
    obtain ⟨l,hl⟩:=ih fun x hx=>h x (List.mem_cons_of_mem _ hx)
    exact ⟨_,((roll_vortex _ _ hk hr).mono (le_max_left k l)).add (hl.mono (le_max_right ..))⟩
lemma senses {s:List (Piece I)} (h : ∀ x∈s, Acts U V x.g) {M : Finset I} (hh : Disjoint M V) (a:ℤ) (r:ℝ) : Acts U V (sum s M a r) := by
  induction s with
  | nil=> exact Eventually.of_forall fun _=>Shape.zero
  | cons i s ih=>
    obtain he:= h i List.mem_cons_self; obtain hp:= ih fun x hx=>h x (List.mem_cons_of_mem _ hx)
    unfold Acts at *; filter_upwards [he,hp] with z he hp
    exact Shape.add (F:=roll M ⟨a,i.l⟩ r i.g z) ((he.move_by M hh r).scale _) hp

lemma congr {F G:ℂ→Cloud I} {k} (h:Vortex k F) (p : F =ᶠ[approaching] G): Vortex k G:= by
  obtain ⟨R,hr,H⟩:= narrow p; exact h.congr hr fun z hz=> (H z hz).symm
end Piece
end YM.MSbar.Pole
