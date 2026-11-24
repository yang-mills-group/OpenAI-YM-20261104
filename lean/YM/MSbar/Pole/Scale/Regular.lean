import YM.MSbar.Pole.Analysis.Scope
import YM.MSbar.Pole.Analysis.Rapid

/-!
# Regular dependence in the dimensional amplitude

Functions of slow growth in external momentum variables and tensor variables, with arbitrary
rapid gain in a subset of free momentum directions marked by the second `Price`. Real C∞ in all
these variables, complex analytic in the dimensional input ε on an open region. Don't attempt
meromorphic dependence by pretending polar expressions have a value at ε=0.
-/

noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A] [NormedSpace ℝ A]

def stretch {E : Type} (p : Price E) : Price (ℂ × E) := ⟨fun i=> p i.2,fun i=>p.large i.2⟩
abbrev strip (E : Type) (U : Set ℂ) := U ×ˢ (univ:Set E)

structure Wall (U : Set ℂ) (p q : Price E) (f : ℂ→E→ℂ) : Prop where
  stream : Packet (strip E U) (stretch p) (stretch q) (fun x => f x.1 x.2)
  region : ∀ z∈U, ∀ x : E, DifferentiableAt ℂ (fun w=> f w x) z

variable {U V : Set ℂ} {p q : Price E} {f g : ℂ→E→ℂ}

namespace Wall
lemma mono (h : Wall U p q f) (hh : V ⊆ U) : Wall V p q f :=
  ⟨h.stream.mono fun _ hx=> ⟨hh hx.1,hx.2⟩, fun z hz x=>h.region z (hh hz) x⟩
lemma eq (o : IsOpen U) (h : Wall U p q f) (hf : EqOn g f U): Wall U p q g := by
  refine ⟨h.stream.congr (fun x hx=> mem_of_superset ((o.prod isOpen_univ).mem_nhds hx)
    (fun i hi=> congr_fun (hf hi.1) i.2)), fun x hx y=> ?_⟩
  exact (h.region x hx y).congr_of_eventuallyEq (mem_of_superset (o.mem_nhds hx) (fun i hi=>congr_fun (hf hi) _))
lemma zero : Wall U p q (0:ℂ→E→ℂ) := ⟨Packet.zero, fun _ _ _ => differentiableAt_const _⟩
lemma add (h : Wall U p q f) (hh : Wall U p q g) : Wall U p q (f+g) :=
  ⟨h.stream.add hh.stream, fun z hz x=> (h.region z hz x).add (hh.region z hz x)⟩
lemma sub (h : Wall U p q f) (hh : Wall U p q g) : Wall U p q (f-g) :=
  ⟨h.stream.sub hh.stream,fun z hz x=> (h.region z hz x).sub (hh.region z hz x)⟩
lemma neg (h : Wall U p q f) : Wall U p q (-f) := ⟨h.stream.neg,fun z hz x=> (h.region z hz x).neg⟩
lemma mul (h : Wall U p q f) (hh : Wall U p 1 g) : Wall U p q (f*g) :=
  ⟨h.stream.mul hh.stream,fun z hz x=> (h.region z hz x).mul (hh.region z hz x)⟩
lemma pays (h : Wall U p q f) (hh : Wall U (p*q) 1 g) : Wall U p q (f*g) :=
  ⟨h.stream.mul_spending hh.stream,fun z hz x=> (h.region z hz x).mul (hh.region z hz x)⟩
lemma sum {Z : Type*} (s : Finset Z) (F : Z → ℂ→E→ℂ) (h : ∀ z ∈ s, Wall U p q (F z)) : Wall U p q (∑ z∈s,F z) := by
  induction s using Finset.induction_on with
  | empty => simpa using Wall.zero
  | @insert z s hz ih => rw [Finset.sum_insert hz]; exact (h z (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma cr (h : Wall U p q f) (x : ℂ × E) (hx : x∈strip E U) : CR (1,0) (Complex.I,0) (fun x => f x.1 x.2) x :=
  (coordinates ((h.stream.smooth _ hx).differentiableAt (by simp))).mpr (h.region _ hx.1 _)

lemma fixed (h : Wall U p q f) {x : ℂ} (hx : x ∈ U) : Packet univ p q (f x) := by
  let E' := ℂ × E; let L : E →L[ℝ] E' := ContinuousLinearMap.inr ℝ ℂ E; let b:E' := (x,0)
  have H(y:E): b+L y=(x,y):=by change (x+0,0+y)=_; simp
  have he := comp_affine_bill L b h.stream (U:=univ) (p:=p) (q:=q) (fun i hi => ?_) ?_ ?_
  · simpa only [H] using! he
  · change b+L i ∈ _; rw [H]; exact ⟨hx,mem_univ _⟩
  · simp_rw [H]; exact Bills.self
  refine bill_byprice fun i _ => ?_; change q _ ≤ stretch q (b+L i); rw [H]
  rfl
lemma freeze {k : E → ℂ} (hh : Packet univ p q k) : Wall U p q (fun _=> k) := by
  refine ⟨?_,fun _ _ _ => differentiableAt_const _⟩
  let L : ℂ×E→L[ℝ]E:= ContinuousLinearMap.snd ..
  have he:= comp_affine_bill L 0 hh (mapsTo_univ _ _) (U:=strip E U) (p:=stretch p) (q:=stretch q) ?_ ?_
  · simpa only [zero_add] using! he
  · simp_rw [zero_add]; exact Bills.self
  refine bill_byprice fun _ _ => ?_; change q _≤ q (0+_); rw [zero_add]; rfl

/-- Scalar dimensional multiplier independent of momenta. -/
lemma formula {k : ℂ→ℂ} (t : Set ℂ) (ht : IsCompact t) (hf : ∀ x∈t,DifferentiableAt ℂ k x)
    (he : ∀ x∈t,ContDiffAt ℝ ∞ k x) (hp : U ⊆ t) : Wall U p 1 (fun z _=> k z) := by
  refine ⟨?_, fun z hz _ => hf _ (hp hz)⟩
  let L : ℂ×E→L[ℝ]ℂ:= ContinuousLinearMap.fst ..
  have hh := comp_affine_bill L 0 (compact_packet (q:=1) ht he) (U:=strip E U) (p:=stretch p) (q:=stretch 1) (fun x hx=> ?_) (Bills.const _) (Bills.const _)
  · simpa only [zero_add] using! hh
  change 0+L x ∈ _; rw [zero_add]; exact hp hx.1
lemma entire {k : ℂ→ℂ} (h : Differentiable ℂ k) (R : ℝ) (hR : ∀ x∈U, ‖x‖ ≤ R) : Wall U p 1 (fun x _=> k x):=
  formula (Metric.closedBall 0 R) (isCompact_closedBall ..) (fun i _=>h i)
    (fun i _ => (show ContDiff ℝ ∞ k from h.contDiff.restrict_scalars ℝ).contDiffAt)
    (fun x hx=> by simpa using hR x hx)
lemma pull (h : Wall U p q f) (L : A→L[ℝ] E) {r s : Price A}
    (hp : Bills univ r 1 (fun x => p (L x))) (hq : Bills univ (q.back L) 1 s.val) :
    Wall U r s (fun z x => f z (L x)) := by
  refine ⟨?_,fun z hz x=>h.region z hz _⟩
  let B : ℂ×A→L[ℝ]ℂ×E:=(ContinuousLinearMap.fst ℝ ℂ A).prod (L.comp (ContinuousLinearMap.snd ..))
  have H (x:ℂ×A): 0+B x=(x.1,L x.2):=by rw [zero_add]; rfl
  have he := comp_affine_bill B 0 h.stream (U:=strip A U) (p:=stretch r) (q:=stretch s) (fun x hx=> ?_) ?_ ?_
  · simpa only [H] using! he
  · change 0+B x∈_; rw [H]; exact ⟨hx.1,mem_univ _⟩
  · simp_rw [H]; exact hp.pull (mapsTo_univ (@Prod.snd ℂ A) _)
  intro k; obtain ⟨C,e,hc,h⟩:=hq k
  refine ⟨C,e,hc,fun x hx=>?_⟩; change ‖s.val x.2‖* 1^k ≤ C * (stretch q (0+B x))^e; rw [H]; exact h _ (mem_univ x.2)
end Wall
end YM.MSbar.Pole
