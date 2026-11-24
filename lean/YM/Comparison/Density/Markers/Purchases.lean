import YM.Comparison.Density.Markers.Identity
import YM.Next.MULTISOURCE.First
import YM.Pert.Attach.Invoice
/-!
# Norm transport at the exact force merger

`HitBudget` charges the marker l1 weights before evaluating the copy
family. Reserve `q` is charged on **each** incoming K entry, vacuum
and marked. A newly merged entry (including a mixed entry with zero
vacuum weight) can afford division precisely because at least one real
flag label is retained; the budget proof uses this in the product. There
is no claim that analytic tail bounds in a regular/path norm supply this
divisor; require the actual K hit from the step. `Origin` can require
any additional fixed set of sites along with the anchor. The support in
perturbative uses must also include every varying address/control, not
just these origin sites; the weight pays on the declared complete support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Markers
open Function Lattice RG Wilson MeasureTheory Filter Marker Finset Pert.Attach
open Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable {A A' : Activities G n} {X : Corrections G n} {p : BudgetPoint}

structure Origin (V : Type) (n : Side) where
  uses : V → Support n
  root : V → Site n
  listed (v) : root v∈uses v

structure BoundTo (K : Supply R G n) (s : ℕ→ Support n) (p : BudgetPoint) (O : Origin V n) : Prop where
  sym i : GaugeInvariant (K i)
  borel i : Measurable (K i)
  reads i : UsesFinal p.threshold (s i) (K i)
  bears i U : Carries O.uses (s i) (K i U)

def ranges (A : Activities G n) (i : ℕ) := (A.forced i).support

structure Manifest (K : Supply R G n) (A : Activities G n) (p : BudgetPoint) (O : Origin V n) : Prop extends BoundTo K (ranges A) p O where
  quiet i U : (K i U).part R.quiet = (A.K i U : ℂ)
  flagged i U : K i U≠0 → (A.forced i).eligible p.threshold U

structure Escort (H : Supply R G n) (X : Corrections G n) (p : BudgetPoint) (O : Origin V n) : Prop extends BoundTo H X.region p O where
  quiet i U : (H i U).part R.quiet=(X.value i U:ℂ)
  flagged i U : Healthy p.threshold (X.region i) U → H i U=0

variable {w : V→ℝ} {K H : Supply R G n} {O : Origin V n}
variable (ha : A.ForcedFamily p) (hx : Pert.Attach.Prepared p.threshold X)
variable (hK : Manifest K A p O) (hH : Escort H X p O)

include hK hH in
private lemma quiet_chain (i : ℕ) (U : Config G n) :
    (chain p A X K H i U).part R.quiet= ((Pert.Attach.attach A X p.threshold A').K i U:ℂ) := by
  change _= ((Pert.Attach.entry A X p.threshold i U:ℝ) : ℂ)
  unfold chain Pert.Attach.entry; split_ifs
  · rw [Multi.quiet_of_prod,Complex.ofReal_prod]; apply Finset.prod_congr rfl; intro j _; cases j; exact hK.quiet ..; exact hH.quiet ..
  simp

include hK hH hx ha
lemma author (A' : Activities G n) :
    Manifest (chain p A X K H) (Pert.Attach.attach A X p.threshold A') p O := by
  let Z:= Pert.Attach.attach A X p.threshold A'
  have HE : Z.ForcedFamily p := Pert.Attach.forced ha hx
  have HP l : BoundTo K (ranges A) p O ∧ GaugeInvariant (fun U=>bonds K H U l) := by
    cases l <;> exact ⟨hK.toBoundTo,by first | exact hK.sym _ | exact hH.sym _⟩
  have HB i U : Carries O.uses (ranges Z i) (∏ j∈parts A X i,bonds K H U j):= by
    refine Carries.prod _ fun j hj=>?_
    have ht : X.area A j ⊆ ranges Z i:= fun u hu=> mem_biUnion.mpr ⟨_,hj,hu⟩
    cases j with
    | inl j=> exact (hK.bears j U).more ht
    | inr j=> exact (hH.bears j U).more ht
  have he i : MeasurableSet {U| (Z.forced i).eligible p.threshold U}:=
    Work.H03.eligible_measurable _ _ (HE.meas_test i)
  exact ⟨⟨fun i z U=> by
    unfold chain; rw [Work.H03.eligible_gauge _ _ _ _ (show (page A X i).extraTest _ ↔ _ from HE.symtest i z U)]; split
    next _=> exact Finset.prod_congr rfl fun j _=> (HP j).2 z U
    rfl,
    fun i=> by
      unfold chain; exact Measurable.ite (he i) (Finset.measurable_fun_prod _ fun j _=> by
        cases j; exact hK.borel _; exact hH.borel _) measurable_const,
    fun i U V h v=> by
      unfold chain; rw [Work.H03.eligible_reads _ (page A X i) (HE.reads_test i) U V h v]; split_ifs
      · refine Finset.prod_congr rfl fun j hj=>?_
        have ht : X.area A j ⊆ ranges Z i:= fun u hu=> mem_biUnion.mpr ⟨_,hj,hu⟩
        cases j
        · exact Work.H03.reads_larger ht (hK.reads _) U V h v
        exact Work.H03.reads_larger ht (hH.reads _) U V h v
      rfl,fun i U=> by unfold chain; split; exact HB i U; exact carry_zero⟩,
    fun i U=> quiet_chain hK hH i U,
    fun i U hh=> by unfold chain at hh; split at hh; assumption; contradiction⟩

omit ha hx hK hH

def HitBudget (p : BudgetPoint) (Ω : ℕ→ Support n) (O : Origin V n) (w : V→ℝ) (ε : ℝ) (K : Supply R G n) (b : ℝ) :=
    ∃ c : ℕ → Poly R, (∀ i U, Over (K i U) (c i)) ∧ (∀ i,Carries O.uses (Ω i) (c i)) ∧ Ac.Hit Ω p.B (Poly.price w ∘ c) (p.supportExponent+ε) b

lemma bound_plain {β : ℝ} {s : ℕ→ Support n} {c : ℕ→ Poly R}
    (hw : ∀ i, 0<w i) (e : ℝ) (he : 0≤e)
    (h : Ac.Hit s p.B (Poly.price w ∘ c) (p.supportExponent+e) β) (x : Site n) :
    SumBudget (fun i=> if x∈s i then p.mass (s i) (Poly.price w (c i)) else 0) β := by
  refine budget_mono (h x) (fun i=>?_) (fun i=>?_)
  · split_ifs; exact mul_nonneg (Real.exp_pos _).le (Poly.nonnegative hw _)
    rfl
  split_ifs
  · dsimp only [comp_apply, BudgetPoint.mass]; rw [mul_comm (Poly.price w _)]; have ht:= Poly.nonnegative hw (c i)
    gcongr; linarith
  rfl

lemma initial_price {X : ℕ→ Support n} (h : ∀ i,(X i).Nonempty) (hw : ∀ i,0<w i) (β e : ℝ) (he : 0≤e)
    (hK : HitBudget p X O w e K β) (U : Config G n) : Summable fun i=> Poly.price w (K i U) := by
  obtain ⟨c,hc,-,hA⟩:=hK
  have hs := Activities.summable_charge h (fun i=> Poly.nonnegative hw _) (bound_plain (p:=p) hw e he hA)
  exact hs.of_nonneg_of_le (fun i=>Poly.nonnegative hw _) fun i=> (hc i U).price hw

lemma vacuum_bound {w' β : ℝ} (A' : Activities G n)
    (hw : ∀ i, 0<w i) (ht : 0≤w') (hK : Manifest K A' p O) (h : HitBudget p (ranges A') O w w' K β) :
    A'.KBound p β := by
  obtain ⟨c,hc,hd,h⟩:= h
  refine ⟨Poly.price w ∘ c,fun i=> ⟨Poly.nonnegative hw _,fun U=> ?_⟩,bound_plain (p:=p) hw _ ht h⟩
  refine le_trans ?_ ((hc _ U).price hw); simpa only [hK.quiet,Poly.quiet_toll,one_mul,Complex.norm_real] using Poly.member hw R.quiet (K i U)

/-- Rooted form, with the OUTPUT forced divisor. No sum over
    all positions of the held root. -/
def MarkBudget (A : Activities G n) (p : BudgetPoint) (O : Origin V n) (w : V→ℝ) (K : Supply R G n) (κ ε : ℝ) := 0<κ ∧ ∃ c : ℕ→Poly R,
    (∀ i U,Over (K i U) (c i)) ∧ (∀ i,Carries O.uses (A.forced i).support (c i)) ∧
      ∀ v : V, SumBudget (fun i : ℕ=> κ⁻¹ * p.mass (A.forced i).support
        (∑ j : R.Mode, if v∈j.val then Poly.toll w j* ‖(c i).part j‖ else 0)) ε

lemma divide_fixed (hw : ∀ i,0<w i) {t β : ℝ} (ht : 0≤ t) {κ : ℝ} (hk : 0<κ) (c : ℕ→Poly R)
    (hA : ∀ i,Carries O.uses (ranges A i) (c i)) (h : Ac.Hit (ranges A) p.B (Poly.price w ∘ c) (p.supportExponent+t) β)
    (v : V) : SumBudget (fun i : ℕ=> κ⁻¹ * p.mass (A.forced i).support
        (∑ j : R.Mode, if v∈j.val then Poly.toll w j* ‖(c i).part j‖ else 0)) (β/κ) := by
  let F (i : ℕ) (j : R.Mode):= if v∈j.val then Poly.toll w j * ‖(c i).part j‖ else 0
  have hj i j : 0≤ F i j:= by unfold F; split; exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _); exact le_rfl
  rw [div_eq_inv_mul]
  apply budget_scale (inv_nonneg.mpr hk.le)
  refine budget_mono (bound_plain (p:=p) hw _ ht h (O.root v)) (fun i=>?_) (fun i=>?_)
  · exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i _=> hj _ i)
  split_ifs with he
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; refine Finset.sum_le_sum fun i _=> ?_; split; rfl; exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _)
  have he' j : F i j=0 := by
     unfold F; split; next hh=> rw [hA _ _ v hh (fun H=> he (H (O.listed _))),norm_zero,mul_zero]
     rfl
  change p.mass _ (∑ j,F _ j)≤ 0; rw [Finset.sum_eq_zero fun j _=> he' j]; unfold BudgetPoint.mass; rw [mul_zero]

lemma divide_forced (hw : ∀ i,0<w i) {t β : ℝ} (ht : 0≤ t) {κ : ℝ} (hk : 0<κ) (h : HitBudget p (ranges A) O w t K β) :
    MarkBudget A p O w K κ (β/κ) := by
  obtain ⟨c,hc,hA,h⟩:=h
  exact ⟨hk,c,hc,hA,fun i=> divide_fixed hw ht hk c hA h i⟩

private lemma forest_price (hw : ∀ i,0<w i) {β q : ℝ} (hq : 1≤q) (ht : 0≤β) (hh : ((p.B+p.B+1:ℕ):ℝ)^4*β ≤ 1)
    (c : Old→ Poly R)
    (W : Old→ℝ) (hW : ∀ i,Poly.price w (c i) ≤ W i) (hQ : ∀ i : ℕ,q*Poly.price w (c (.inl i)) ≤ W (.inl i))
    (hs : Ac.Hit (X.area A) p.B W (p.supportExponent+1) β) :
    Ac.Hit (ranges (Pert.Attach.attach A X p.threshold A')) p.B
      (Poly.price w ∘ fun i=>∏ j∈parts A X i,c j) p.supportExponent ((Real.exp β-1)/q) := by
  have hg j : 0≤ W j:= (Poly.nonnegative hw _).trans (hW _)
  intro i
  rw [div_eq_inv_mul]; apply budget_mono (budget_scale (inv_nonneg.mpr (zero_le_one.trans hq)) (budget_pull _ (parts_inj A X) (Ac.forest (X.area A) p.B p.exponent_pos.le hg hs hh ht i)))
  · intro j; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; rfl
  intro j
  unfold Ac.roots
  simp only [Function.comp_apply,ite_and]
  rw [if_pos (show Ac.Spark (X.area A) (parts A X j) from decoding A X j|>.2.1)]
  have H : ranges (Pert.Attach.attach A X p.threshold A') j=(parts A X j).biUnion (X.area A):= rfl
  rw [H]; split_ifs
  · rw [mul_left_comm,mul_comm _ (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [← div_eq_inv_mul]; refine (le_div_iff₀' (zero_lt_one.trans_le hq)).2 ?_
    calc _ ≤ q*(∏ i∈parts A X j,Poly.price w (c i)) := mul_le_mul_of_nonneg_left (Poly.multiple hw ..) (zero_le_one.trans hq)
         _ ≤ _ := by
           obtain ⟨u,hu⟩:= (decoding A X j).2.2.1
           have he : (Sum.inl u:Old) ∈ parts A X j:= mem_toLeft.mp hu
           rw [← Finset.mul_prod_erase _ _ he, ← Finset.mul_prod_erase _ W he, ← mul_assoc]
           exact mul_le_mul (hQ u) (prod_le_prod (fun i _=> Poly.nonnegative hw _) (fun i _=>hW _)) (prod_nonneg fun i _=> Poly.nonnegative hw _) (hg _)
  rw [mul_zero]

def tile (A : Activities G n) (X : Corrections G n) (c d : ℕ→Poly R) (i : ℕ) :=
    ∏ j∈parts A X i, Sum.elim c d j
lemma tile_carries (A : Activities G n) (X : Corrections G n) (c d : ℕ→Poly R)
    (hF : ∀ i,Carries O.uses (ranges A i) (c i)) (hM : ∀ i,Carries O.uses (X.region i) (d i))
    (p : BudgetPoint) (i : ℕ) (A': Activities G n) : Carries O.uses (ranges (Pert.Attach.attach A X p.threshold A') i) (tile A X c d i) := by
  refine Carries.prod _ fun j hj=> ?_
  have hp : X.area A j ⊆ ranges (Pert.Attach.attach A X p.threshold A') i:= fun v hv=>mem_biUnion.mpr ⟨j,hj,hv⟩
  cases j; exact (hF _).more hp; exact (hM _).more hp
lemma tile_over (K H : Supply R G n) (p : BudgetPoint) {c d : ℕ→Poly R}
    (hc : ∀ i U, Over (K i U) (c i)) (hd : ∀ i U, Over (H i U) (d i)) (i U) : Over (chain p A X K H i U) (tile A X c d i):= by
  have hX j : Over (bonds K H U j) (Sum.elim c d j):=j.rec (fun i=>hc i U) (fun i=>hd i U)
  unfold chain; split
  · exact Over.prod _ fun j _=> hX j
  exact (Over.prod (parts A X i) fun j _=> hX j).zeroLeft
lemma tile_cost (hw : ∀ i,0<w i) {a b β q : ℝ}
    (hq : 1≤q) (ht : 0≤β) (hh : ((p.B+p.B+1:ℕ):ℝ)^4*β ≤ 1) (he : q*a+b≤β)
    {c d : ℕ→Poly R} (h : Ac.Hit (ranges A) p.B (Poly.price w ∘ c) (p.supportExponent+1) a) (hy : Ac.Hit X.region p.B (Poly.price w ∘ d) (p.supportExponent+1) b) (A' : Activities G n) :
    Ac.Hit (ranges (Pert.Attach.attach A X p.threshold A')) p.B (Poly.price w ∘ tile A X c d) p.supportExponent ((Real.exp β-1)/q) := by
  let f:= Sum.elim c d
  let W:= Sum.elim (fun i=>q*Poly.price w (c i)) (fun i=>Poly.price w (d i))
  refine forest_price hw hq ht hh f W (fun j=> j.rec (fun i=> le_mul_of_one_le_left (Poly.nonnegative hw _) hq) (fun _=>le_rfl)) (fun _=>le_rfl) ?_
  intro x
  apply budget_loosen (C:=q*a+b) _ he
  apply Pert.Attach.split_budget _ (hy x)
  let L:=fun i:ℕ=> q*(if x∈ranges A i then (Poly.price w ∘ c) i*Real.exp ((p.supportExponent+1)*coverNumber p.B (ranges A i)) else 0)
  convert budget_scale (x:=q) (zero_le_one.trans hq) (h x) using 2
  rename_i i; change (if x∈ranges A i then (q* _)*_ else 0)=L i; unfold L; split_ifs
  · rw [mul_assoc]; rfl
  rw [mul_zero]

lemma tile_payment (hw : ∀ i,0<w i) {a b β q : ℝ}
    (hq : 1≤q) (ht : 0≤β) (hh : ((p.B+p.B+1:ℕ):ℝ)^4*β ≤ 1) (he : q*a+b≤β)
    (hK : HitBudget p (ranges A) O w 1 K a) (hH : HitBudget p X.region O w 1 H b) :
    HitBudget p (ranges (Pert.Attach.attach A X p.threshold A')) O w 0 (chain p A X K H) ((Real.exp β-1)/q) := by
  obtain ⟨c,hc,hF,h⟩:= hK
  obtain ⟨d,hd,hM,hy⟩:= hH
  exact ⟨_,tile_over K H p hc hd,fun i=> tile_carries A X c d hF hM p i A',by rw [add_zero]; exact tile_cost hw hq ht hh he h hy A'⟩

/-- Spend multiple exponent reserves without pretending to have a different
History BudgetPoint. -/
def later (p : BudgetPoint) (ε : ℝ) (he : 0≤ε) : BudgetPoint:=
    {p with supportExponent := p.supportExponent+ε, exponent_pos := add_pos_of_pos_of_nonneg p.exponent_pos he}

lemma late_iff {e x d : ℝ} (hp : 0 ≤ e) (Y : ℕ→Support n) :
    HitBudget p Y O w (e+x) K d ↔ HitBudget (later p e hp) Y O w x K d := by simp only [HitBudget,later,add_assoc]

theorem respects (hw : ∀ i,0<w i) {a b β q e: ℝ} (hE : 0 ≤ e)
    (hq : 1≤q) (ht : 0≤β) (hh : ((p.B+p.B+1:ℕ):ℝ)^4*β ≤ 1) (he : q*a+b≤β)
    (hK : HitBudget p (ranges A) O w (e+1) K a) (hH : HitBudget p X.region O w (e+1) H b) :
    HitBudget p (ranges (Pert.Attach.attach A X p.threshold A')) O w e (chain p A X K H) ((Real.exp β-1)/q) := by
  have hK := (late_iff hE _).1 hK
  have hX := (late_iff hE _).1 hH
  simpa only [add_zero] using! (late_iff hE _).2 (tile_payment (A':=A') hw hq ht hh he hK hX)
end YM.Comparison.Density.Markers
