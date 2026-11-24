import YM.OPE.Compatible.Trees.Induct

/-!
# The finite nested evaluation and its priced error

Exact sequential definition. Evaluate all vertices in this *fixed*
postorder (children necessarily before parent), branching each time into
all the physical labels through that vertex's horizon. Multiply that
choice's coefficient into the result (while retaining the **declared**
radii and geometry throughout), add all. At the root read just the chosen
coefficient. `bud` = one maximal nonroot
vertex still not pruned. `shoot` there is on exactly its strictChildren. Trimming
it thus deletes just that vertex from the set of *remaining* internals;
in the remaining leaf slots v replaces its strictChildren with that term's field
label. No other change to any labels or locations. The final nontruncated
step reads the coefficient at the root's children. (Use at `Crown` only.)

Charge: any common gain γ ≤ (D_v+1)jump for all v in remaining. If some
edge gives 0 gain in this layer (i.e. not a genuine exponential drop) naive
bound enough. Otherwise use splice at arbitrary high intermediate horizon.
After the signed exchange, the cost of every discarded high term is paid
by that one edge. Pass the remaining error gain as-is through this degree,
keeping the cuts' weights. In particular in `nests_cost`, even when P is
just the root the result is valid for *any* γ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V)
    {G:Gauge} {C:Family G} {F:Extraction.Order} {S:Table C.book} (U:Spec.Final C F S)
    {l:Type}{φ:Filter l} [φ.NeBot]{T:l→ℝ} {t:V→ℝ}{s:l→ V→ ℝ}{X:l→ V→ E4}
    {M η:ℝ}(L:Layer E φ T M η t s X)(Z: Services C F S)
    (D:V→ℕ) (P:Finset V)(H:Crown P) (a:Tones U)(p:V→ S.Tag)

/-- Postorder evaluation. Can use on any valid cut. -/
def nests (P:Finset V) (a:Tones U) (s:V→ℝ) (x:V→ E4) (p:V→ S.Tag) : ℂ := if h:(rest P).Nonempty then
    let v:= bud P h
    ∑ b∈ shades (facets U) (D v), shoot E U P v b s x p * nests (trim P v) a s x (paint U v p b)
  else frontierCoefficient E U P a s x p
termination_by P.card
decreasing_by exact Finset.card_lt_card (lighter _ (bud_live ..))

include H
-- usage note: show the formulas literally with `strictChildren` not recursive cuts.
omit H in
lemma shoot_at_bud (h : (rest P).Nonempty) (s:V→ ℝ)(x:V→ E4) : let v:=bud P h
    shoot E U P v a s x p=beam U a (s v) (picked (strictChildren E v) x) (picked (strictChildren E v) p) (x v) := by
  intro v; unfold shoot; rw [glen_kids E P (bud_tip P h)]
omit [Fintype V] H in
lemma trim_bud (h : (rest P).Nonempty) : trim P (bud P h)=P.erase (bud P h) := by
  ext v; rw [Finset.mem_erase, trim, Finset.mem_filter]; constructor
  · rintro ⟨hi,he⟩; exact ⟨fun e => he e.ge,hi⟩
  rintro ⟨hi,hv⟩; exact ⟨hv,fun e => hi (le_antisymm ((bud_tip ..).2 hv e) e)⟩
lemma bare (h : ¬ (rest P).Nonempty) (s:V→ℝ)(x:V→E4) :
    frontierCoefficient E U P a s x p=beam U a (s ⊥) (picked (strictChildren E ⊥) x) (picked (strictChildren E ⊥) p) (x ⊥) := by
  unfold frontierCoefficient; rw [(tiny E P H h).2]
/-- Tags supplied on *leaf slots*. Values elsewhere don't matter. -/
lemma nests_picked (s:V→ℝ) (x:V→E4) (q:V→ S.Tag) (h:picked (brim E P) p=picked (brim E P) q) :
    nests E U D P a s x p=nests E U D P a s x q := by
  revert H p q; apply Finset.lt_wf.induction P
  intro P ih H p q h
  by_cases hp : (rest P).Nonempty
  · let v := bud P hp
    rw [nests, dif_pos hp,nests, dif_pos hp]; exact Finset.sum_congr rfl fun b _ => by
      have hu : picked (glen E P v) p = picked (glen E P v) q := funext fun i =>
        congr_fun h (⟨i.val,(Finset.mem_filter.mp i.2).1⟩:↑(brim E P))
      change shoot E U P v b s x p * nests _ _ _ (trim P v) _ _ _ (paint _ _ p _) =
        shoot E U P v b s x q * nests _ _ _ (trim P v) _ _ _ (paint _ _ q _)
      unfold shoot; rw [hu]; refine congr_arg _ (ih _ (lighter _ (bud_live _ hp))
        (remains _ H (bud_trunk _ hp)) _ _ ?_); ext1 i; change paint U v p b i.val=paint U v q b i.val
      rcases (frontier_trim E P H (bud_trunk P hp) (bud_live P hp)).mp i.2 with he | he
      · simp [show i.val=v from he,paint]
      have ht : i.val≠v := fun e => he.2 e.ge
      rw [paint,update_of_ne ht,paint,update_of_ne ht]; exact congr_fun h ⟨_,he.1⟩
  rw [nests,dif_neg hp,nests,dif_neg hp]; unfold frontierCoefficient; rw [h]

include Z L
lemma naive : RateLE φ T (fun i=>nests E U D P a (s i) (X i) p) (demand E P p t a.fst) := by
  revert H p; apply Finset.lt_wf.induction P
  intro P ih H p
  by_cases h:(rest P).Nonempty
  · conv => arg 3; ext i; rw [nests,dif_pos h]
    exact RateLE.sum L.flow fun b hb => zip_pay E U L Z P H p
      (bud_light P t (bud_tip P h)) (bud_mem ..) b a.fst _
      (ih _ (lighter _ (bud_live _ h)) (remains _ H (bud_trunk _ h)) (paint U (bud P h) p b))
  conv => arg 3; ext i; rw [nests,dif_neg h]
  exact direct_cost E U L Z P H p a
lemma nests_cost {γ:ℝ}(hg:0 ≤ γ)(h:∀ v∈rest P,γ ≤ (D v+1:ℝ)*jump E t v) : RateLE φ T
    (fun i=> frontierCoefficient E U P a (s i) (X i) p - nests E U D P a (s i) (X i) p) (demand E P p t a.fst-γ) := by
  rcases hg.lt_or_eq with hg|hg
  · revert H p h; apply Finset.lt_wf.induction P
    intro P ih H p h
    by_cases hx : (rest P).Nonempty
    · let v:= bud P hx; have hv : v∈rest P := bud_mem ..
      have he := h v hv
      have hδ : 0<jump E t v := pos_of_mul_pos_right (lt_of_lt_of_le hg he) (by positivity)
      have hq : Light P t v:= bud_light P t (bud_tip P hx)
      obtain ⟨m,hm,hD⟩ := ((buys E U L Z P H p hv hq hδ a (demand E P p t a.fst-γ)).and
        (eventually_ge_atTop (D v))).exists
      let S := shades (facets U) (D v)
      let W := shades (facets U) m
      have hw : S⊆W := fun b hb=> (shadows ..).mpr (((shadows ..).mp hb).trans hD)
      let z (b:Tones U)(i:l) := frontierCoefficient E U (trim P v) a (s i) (X i) (paint U v p b)
      let r (b:Tones U)(i:l) := nests E U D (trim P v) a (s i) (X i) (paint U v p b)
      let f (b:Tones U)(i:l):= shoot E U P v b (s i) (X i) p
      have hh (b:Tones U)(hb:b∈ W\S) : RateLE φ T (fun i=> f b i * z b i) (demand E P p t a.fst-γ) := by
        have he' := (shoot_rate E U L Z P H p (Finset.mem_erase.mp hv).2 hq b).mul
          (direct_cost E U L Z (trim P v) (remains _ H (bud_trunk P hx)) (paint U v p b) a)
        rw [gross E U P H p hq hv] at he'
        have ht : D v+1 ≤ b.fst := Nat.succ_le_iff.mpr (lt_of_not_ge (mt (shadows ..).mpr (Finset.mem_sdiff.mp hb).2))
        exact he'.mono (sub_le_sub_left (he.trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hδ.le)) _)
      have hl (b:Tones U) : RateLE φ T (fun i=> f b i * (z b i - r b i)) (demand E P p t a.fst-γ) :=
        ((shoots_with E U L Z P H p hq hv b a.fst (fun i=> z b i-r b i)
          (ih _ (lighter _ (bud_live P hx)) (remains _ H (bud_trunk P hx)) (paint U v p b) fun j hj=> h j
            (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,(Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1⟩))).mono
            (sub_le_sub_right (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hδ.le)) _))
      refine ((hm.add (RateLE.sum L.flow hh) L.flow).add
        (RateLE.sum (S:=S) L.flow fun i _=> hl i) L.flow).congr (Eventually.of_forall fun i => ?_)
      dsimp only; rw [nests, dif_pos hx]
      change frontierCoefficient E U P a (s i) (X i) p - (∑ b∈ W, f b i * z b i)+ (∑ b∈ W\S,f b i*z b i)+
        (∑ b∈ S, f b i*(z b i-r b i)) = frontierCoefficient E U P a (s i) (X i) p- (∑ b∈S,f b i*r b i)
      rw [← Finset.sum_sdiff hw]; simp_rw [mul_sub, Finset.sum_sub_distrib]; abel
    conv => arg 3; ext i; rw [nests,dif_neg hx,sub_self]
    exact RateLE.zero _ _ _
  rw [← hg,sub_zero]
  exact (direct_cost E U L Z P H p a).sub (naive E U L Z D P H a p) L.flow
end YM.OPE.Arboreal
