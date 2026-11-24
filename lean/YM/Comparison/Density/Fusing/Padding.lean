import YM.Comparison.Density.Fusing.Alphabet
import YM.Push.ABSOLUTE_SUMS.Array

/-!
Some marked flag-only log changes can be asymmetric on held geometry
(registering an anchor, address, differentiated test). This must not
break `Valid.Moves` of the underlying vacuum labels. Pad the correction
alphabet by complete finite permutations at this period. No hit cost
for the unused zero entries; the old predicate and Steps under marker
restriction are kept.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Fusing.Pads
open Testing Markers Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side} {B : BudgetPoint}
variable {X : V→Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable {O : Readers V X n} {w : V→ℝ}

structure Main (Y : Corrections G n) (B : BudgetPoint) : Prop extends Prepared B.threshold Y where
  filled i : (Y.region i).Nonempty

structure Extras (A : ι → Support n) (F : ι → Cross X → Config G n→ Poly R) (B : BudgetPoint) (O : Readers V X n) : Prop where
  filled i : (A i).Nonempty
  ticket i U : Catalogue O.locus (A i) (fun x=> F i x U)
  anchors i x U : Carries O.source.uses (A i) (F i x U)
  marks i x U : (F i x U).part R.quiet=0
  sym i x : GaugeInvariant (F i x)
  meas i x : Measurable (F i x)
  reads i x : UsesFinal B.threshold (A i) (F i x)
  heals i x U : Healthy B.threshold (A i) U → F i x U=0

abbrev Slot (ι : Type) (n : Side) := ι × Equiv.Perm (Site n)

variable (Y : Corrections G n) (A : ι→ Support n)

def locate (ι : Type) [Countable ι] (n : Side) : ℕ≃ (ℕ⊕ Slot ι n) := by
  let S:= ℕ⊕ Slot ι n
  haveI : Infinite S := Infinite.of_injective (.inl : ℕ→S) Sum.inl_injective
  haveI : Encodable S := Encodable.ofCountable _
  letI : Denumerable S := Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv S).symm
variable [Countable ι]
def spot (z : Slot ι n) := (A z.1).image z.2
omit [Countable ι] in
lemma actual (i) : spot A (i,Equiv.refl _)=A i:=by simp [spot]

def era : Corrections G n := ⟨Sum.elim Y.region (spot A) ∘ locate ι n, Sum.elim Y.value (fun _=>0) ∘ locate ι n⟩
variable (F : ι → Cross X→Config G n→Poly R)

def echo {Z : Type*} [Zero Z] {n : Side} (k : ι→ Z) (z : Slot ι n) :=
    if z.2=Equiv.refl _ then k z.1 else 0

def insertions : Leftovers R X G n where
  real := era Y A
  marked x i U := (locate ι n i).elim (fun _=>0) (echo (fun s=> F s x U))
variable {Y A F}

private def run (x : Site n) (s : Signed) : Slot ι n≃ Slot ι n:=
    let R:= s.actEquiv.toEquiv.trans (Equiv.addRight x)
    Equiv.prodCongr (Equiv.refl _) (Equiv.mulLeft R)
omit [Countable ι] in
private lemma run_toll (x : Site n) (s : Signed) (z : Slot ι n): spot A (run x s z)= (spot A z).image (affine s x):= by
  unfold spot run; rw [image_image]; rfl

variable (h : Main Y B) (hp : Extras A F B O)
include h hp
lemma corrected : Placed B O (insertions Y A F):= by
  have he := h.toPrepared
  have hn i : ((insertions Y A F).real.region i).Nonempty:= by
    change (Sum.elim Y.region (spot A) (locate ι n i)).Nonempty; cases locate ι n i; exact h.filled _; exact (hp.filled _).image _
  have hk : Prepared B.threshold (era Y A) := by
    refine ⟨fun i U=> ?_,fun i=>?_,fun i=>?_,fun i=>?_,fun s x=> ?_⟩
    · simp only [era, Function.comp_apply]; cases locate ι n i; exact fun ha=> he.flag _ U ha; exact fun _=>rfl
    · simp only [era, Function.comp_apply]; cases locate ι n i; exact he.sym _; exact fun _ _=>rfl
    · simp only [era, Function.comp_apply]; cases locate ι n i; exact he.meas _; exact measurable_const
    · simp only [era, Function.comp_apply]; cases locate ι n i; exact he.deps _; exact fun _ _ _ _=>rfl
    obtain ⟨v⟩:= he.move s x
    let p:=(locate ι n); let q:= Equiv.sumCongr v.perm (run (ι:=ι) x s)
    refine ⟨(p.trans q).trans p.symm,fun i=>?_,fun i U=>?_⟩
    · simp only [era,Function.comp_apply,p,Equiv.trans_apply,Equiv.apply_symm_apply]; cases locate ι n i with
      | inl i=> exact v.region i
      | inr i=> exact run_toll x s i
    simp only [era,Function.comp_apply,p,Equiv.trans_apply,Equiv.apply_symm_apply]; cases locate ι n i; exact v.value _ U; rfl
  refine ⟨hn,hk,fun x=>?_,fun x i U=>?_,fun x i U=>?_,fun i U=>?_⟩
  · constructor
    · intro i; unfold insertions echo; dsimp only
      cases locate ι n i <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
      · exact fun _ _=>rfl
      split; exact hp.sym _ x; exact fun _ _=>rfl
    · intro i; unfold insertions echo; dsimp only; cases locate ι n i
      · exact measurable_const
      dsimp only [Sum.elim_inr]; split; exact hp.meas _ _; exact measurable_const
    · rintro i; unfold insertions echo; dsimp only [era,comp_apply]; cases locate ι n i
      · exact fun _ _ _ _=> rfl
      dsimp only [Sum.elim_inr]; split
      next hx=> simp only [spot,hx,Equiv.coe_refl,image_id]; exact hp.reads _ _
      exact fun _ _ _ _=> rfl
    · intro i U; unfold insertions echo; dsimp only [era,comp_apply]; cases locate ι n i; exact carry_zero
      dsimp only [Sum.elim_inr]; split
      next hx=> simp only [spot,hx,Equiv.coe_refl,image_id]; exact hp.anchors _ x U
      exact carry_zero
  · unfold insertions echo; dsimp only; cases locate ι n i; exact Poly.part_nil _
    dsimp only [Sum.elim_inr]; split; exact hp.marks ..; exact Poly.part_nil _
  · unfold insertions echo; dsimp only [era, comp_apply]; cases locate ι n i; exact fun _=>rfl
    dsimp only [Sum.elim_inr]; split; next hx=> rw [spot,hx]; simp only [Equiv.coe_refl,image_id]; exact hp.heals _ x U
    exact fun _=>rfl
  unfold insertions echo; dsimp only [era,comp_apply]; cases locate ι n i; exact Catalogue.empty
  dsimp only [Sum.elim_inr]; split
  next hx=> simp only [spot,hx,Equiv.coe_refl,image_id]; exact hp.ticket _ U
  exact Catalogue.empty

omit hp h [∀ v, NormedSpace ℂ (X v)] in
lemma compensate {e a b : ℝ} (L : ℕ→ℝ) (M : ι→Poly R)
    (h : ∀ i U, |Y.value i U| ≤ L i) (hX : ∀ i,Carries O.source.uses (A i) (M i)) (hz : ∀ i,(M i).part R.quiet=0)
    (hS : ∀ x : Cross X, UnitPage x → ∀ i U, Over (F i x U) (M i))
    (he : Ac.Hit Y.region B.B L (B.supportExponent+e) a) (hh : Ac.Hit A B.B (Poly.price w ∘ M) (B.supportExponent+e) b)
    (hw : ∀ x,0<w x): Compensated B O (insertions Y A F) w e (a+b):= by
  let f:=(fun j:ℕ⊕Slot ι n=> Sum.elim L (fun _=>0) j)
  let g:=(fun j:ℕ⊕Slot ι n=> Sum.elim (fun _=>0) (echo M) j)
  let s:=Sum.elim Y.region (spot A)
  have ht x : SumBudget (fun i:Slot ι n=> if x ∈ spot A i then Poly.price w (echo M i) * Real.exp ((B.supportExponent+e)*coverNumber B.B (spot A i)) else 0) b:= by
    refine budget_rows _ _ (fun i=>budget_finite (fun j=> ?_) ?_) (hh x)
    · split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
    rw [sum_eq_single (Equiv.refl _),actual, echo]; simp only [↓reduceIte]; exact le_rfl
    · intro j _ hj; unfold echo; dsimp only; rw [if_neg hj]; split; rw [Poly.zero_price, zero_mul]; rfl
    simp
  refine ⟨f ∘ locate ι n,g ∘ locate ι n,fun i U=>?_,fun i=>?_,fun i=>?_,fun x hx i U=>?_,fun x=> ?_⟩
  · dsimp only [insertions,era,comp_apply,f]; cases locate ι n i; exact h ..; exact (by change |(0:ℝ)| ≤ 0; simp)
  · dsimp only [insertions,era,comp_apply,g]; cases locate ι n i; exact carry_zero
    unfold echo; dsimp only [Sum.elim_inr]; split
    next hx=> simp only [spot,hx, Equiv.coe_refl,image_id]; exact hX _
    exact carry_zero
  · dsimp only [comp_apply,g]; cases locate ι n i; rfl
    unfold echo; dsimp only [Sum.elim_inr]; split; exact hz _; exact rfl
  · have he : Over (0:Poly R) 0:= by simpa using (over_unit (R:=R)).scale (s:=0) (t:=0) (by simp)
    simp only [insertions,comp_apply,g]; cases locate ι n i; exact he
    unfold echo; dsimp only [Sum.elim_inr]; split; exact hS x hx _ U; exact he
  let ψ (i : ℕ⊕Slot ι n):= if x ∈ s i then (f i+Poly.price w (g i))*Real.exp ((B.supportExponent+e)*coverNumber B.B (s i)) else 0
  have hψ: SumBudget ψ (a+b) := by
    apply budget_of_sum
    · intro i; cases i <;> simp only [ψ,f,g,s,Sum.elim_inl, Sum.elim_inr, Poly.zero_price, add_zero,zero_add]
      · exact (he _).1 _
      exact (ht _).1 _
    intro r; rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]; simp only [ψ,f,g,s,Sum.elim_inl, Sum.elim_inr, Poly.zero_price,add_zero,zero_add]
    exact add_le_add (budget_sum (he x) _) (budget_sum (ht x) _)
  exact budget_pull _ (locate ι n).injective hψ

omit h hp
omit [Countable ι] in
lemma echo_sum {Z : Type*} [NormedAddCommGroup Z] {k : ι→Z} {d : Z} (h : HasSum k d) (n : Side) : HasSum (echo (n:=n) k) d := by
  let p:= fun i:ι=> (i,Equiv.refl (Site n))
  have he : Injective p:= Prod.mk_left_injective ..
  rw [← he.hasSum_iff]
  · simpa only [p, echo, comp_def,↓reduceIte] using h
  rintro ⟨x,y⟩ hp; unfold echo; apply if_neg
  dsimp only; rintro rfl; exact hp ⟨x,rfl⟩

lemma real_total (Y : Corrections G n) (A : ι→ Support n) (U : Config G n) {e : ℝ} (H : HasSum (fun i=> Y.value i U) e) :
    HasSum (fun i=> (era Y A).value i U) e := by
  let f:= fun i:ℕ⊕Slot ι n=> Sum.elim Y.value (fun _=>0) i U
  rw [← add_zero e]; change HasSum (f ∘ locate ι n) (e+0); rw [(locate ι n).hasSum_iff]; apply HasSum.sum (f:=f) H; exact (show HasSum (fun i:Slot ι n=> (0:ℝ)) 0 from hasSum_zero)

omit [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)] in
lemma marked_total (Y : Corrections G n) (A : ι→ Support n) (x : Cross X) (U : Config G n) {e : Poly R}
    (H : HasSum (fun i=> F i x U) e) : HasSum (fun i=> (insertions Y A F).marked x i U) e := by
  let f:= fun i:ℕ⊕Slot ι n=> i.elim (fun _=>0) (echo fun j=> F j x U)
  rw [← zero_add e]; exact (locate ι n).hasSum_iff.mpr (HasSum.sum (f:=f) hasSum_zero (echo_sum H n))
end YM.Comparison.Density.Fusing.Pads
