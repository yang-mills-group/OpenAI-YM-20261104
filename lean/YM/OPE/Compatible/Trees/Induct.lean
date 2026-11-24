import YM.OPE.Compatible.Trees.Weight

/-!
# Direct rate statements by induction on the cut

Critical to estimate the projection on full frontier, not the discrepancy
itself with arbitrary exteriors using a horizon that has to work for future
unknown demands. Estimate signed combination too. In `balance_cost`, after
projecting signed kernel to get signed ray comparison, subtract the tested
signed ray from signed product. The rest of the sum pays the costs of
ordinary expansions on smaller tree cuts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V)
    {G:Gauge} {C:Family G} {F:Extraction.Order} {S:Table C.book} (U:Spec.Final C F S)
    {l:Type}{φ:Filter l} [φ.NeBot]{T:l→ℝ} {t:V→ℝ}{s:l→ V→ ℝ}{X:l→ V→ E4}
    {M η c:ℝ}(L:Layer E φ T M η t s X)(Z: Services C F S)
    (P:Finset V)(H:Crown P)(p:V→ S.Tag)

include Z L H
lemma buys {v:V}(hv:v∈rest P) (h:Light P t v)(he:0<jump E t v)(a:Tones U)(κ:ℝ) :
    ∀ᶠ n:ℕ in atTop, RateLE φ T (fun i=>
      frontierCoefficient E U P a (s i) (X i) p - ∑ b∈ shades (facets U) n,
        shoot E U P v b (s i) (X i) p * frontierCoefficient E U (trim P v) a (s i) (X i) (paint U v p b)) κ := by
  filter_upwards [investment E he ((bill (picked (glen E P v) p):ℝ)*t v+(bill (picked (shore E P v) p):ℝ)
      + palm (supplies S) a.fst) κ] with n hn
  exact (spliced_coeff E U L Z P H hv h he p n a).mono (by linarith only [hn])

lemma direct_cost (a:Tones U) : RateLE φ T (fun i=>frontierCoefficient E U P a (s i) (X i) p) (demand E P p t a.fst) := by
  revert H p; apply Finset.lt_wf.induction P
  intro P ih H p
  rcases Light.may E L P H with h|⟨v,hv,h,hδ⟩
  · exact same_light E U L Z P H h p a
  obtain ⟨n,hp⟩ := (buys E U L Z P H p hv h hδ a (demand E P p t a.fst)).exists
  exact (hp.add (RateLE.sum (S:=shades (facets U) n) L.flow fun b _ =>
    zip_pay E U L Z P H p h hv b a.fst _
      (ih _ (lighter P (Finset.mem_erase.mp hv).2) (remains _ H (Finset.mem_erase.mp hv).1)
        (paint U v p b))) L.flow).congr (Eventually.of_forall fun _ => sub_add_cancel ..)

variable {J:Type} [Fintype J] {Y:l→ J→ E4} (q:J→ S.Tag) (r:l→ Viewers U)(n:ℕ)
variable (hc:0<c) (hy:∀ᶠ i in φ, ClearOf (X i ⊥) (Y i) c)

/-- at ungated ray, in the viewer's full system -/
def balance (P:Finset V)(r:Viewers U)(n:ℕ)(x:V→ E4)(p:V→ S.Tag)(y:J→ E4)(q:J→ S.Tag) :=
  kernel (spectator U r) (beside (picked (brim E P) x) y) (beside (picked (brim E P) p) q) -
    Cov.insert S (spectator U r) (x ⊥) y q n (ray U n (picked (brim E P) x) (picked (brim E P) p) (x ⊥))

include q hc hy r
lemma light_balanced (h:Light P t ⊥) : RateLE φ T (fun i=>balance E U P (r i) n (X i) p (Y i) q)
      (demand E P p t (n+1:ℝ)) := by
  have hx:= L.at_base E P H h
  unfold balance demand
  rw [payload_light E P h]
  rcases (L.bounds _ L.canopy).1.lt_or_eq with hp|he
  · obtain ⟨hw,hq⟩ := free_clear L.flow hc hy
    have ht := single_rate U Z L.flow (picked (brim E P) p) q r hx
        (L.enveloped E (Subtype.val: ↑(brim E P)→V) L.canopy fun _=>bot_le) hq hp le_rfl hw le_rfl n
    rwa [mul_zero,add_zero,sub_zero] at ht
  rw [← he,mul_zero,mul_zero,sub_self]; rw [← he] at hx
  exact single_shallow U Z L.flow (picked (brim E P) p) q r hx
    (L.inch E (Subtype.val: ↑(brim E P)→V) L.canopy fun _=>bot_le) hy hc n

lemma futures {v:V}(hv:v∈rest P) (h:Light P t v)(he:0<jump E t v)(κ:ℝ) :
    ∀ᶠ m:ℕ in atTop, RateLE φ T (fun i=>
      balance E U P (r i) n (X i) p (Y i) q - ∑ b∈ shades (facets U) m,
        shoot E U P v b (s i) (X i) p * balance E U (trim P v) (r i) n (X i) (paint U v p b) (Y i) q) κ := by
  filter_upwards [investment E he ((bill (picked (glen E P v) p):ℝ)*t v+(bill (picked (shore E P v) p):ℝ)
      + bill q) κ, investment E he ((bill (picked (glen E P v) p):ℝ)*t v+(bill (picked (shore E P v) p):ℝ)
      + palm (supplies S) n) κ] with m hm hκ
  have he' := (splice E U L Z P H hv h he p m q r hc hy).mono (show _ ≤ κ by linarith only [hm])
  have hg := (slice_ray E U L Z P H hv h he p m n).mono (show _ ≤ κ by linarith only [hκ])
  obtain ⟨hw,hq⟩:= free_clear L.flow hc hy
  have hb := count_insert U Z L.flow n _ q r hq le_rfl hw le_rfl hg
  rw [mul_zero,mul_zero,add_zero,add_zero] at hb
  refine (he'.sub hb L.flow).congr (Eventually.of_forall fun i => ?_)
  dsimp only; unfold balance
  rw [map_sub,map_sum]; simp_rw [map_smul,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]; abel

lemma balance_cost : RateLE φ T (fun i=> balance E U P (r i) n (X i) p (Y i) q)
    (demand E P p t (n+1:ℝ)) := by
  revert H p; apply Finset.lt_wf.induction P
  intro P ih H p
  rcases Light.may E L P H with h|⟨v,hv,h,hδ⟩
  · exact light_balanced E U L Z P H p q r n hc hy h
  obtain ⟨m,hp⟩ := (futures E U L Z P H p q r n hc hy hv h hδ (demand E P p t (n+1:ℝ))).exists
  exact (hp.add (RateLE.sum (S:=shades (facets U) m) L.flow fun b _ =>
    zip_pay E U L Z P H p h hv b _ _
      (ih _ (lighter P (Finset.mem_erase.mp hv).2) (remains _ H (Finset.mem_erase.mp hv).1)
        (paint U v p b))) L.flow).congr (Eventually.of_forall fun _ => sub_add_cancel ..)

omit r in
lemma drift_cost : RateLE φ T (fun i=> drift U n (s i ⊥) (picked (brim E P) (X i))
    (picked (brim E P) p) (X i ⊥) (Y i) q) (demand E P p t (n+1:ℝ)) :=
  price_from_viewers U _ _ _ _ _ _ _ (L.words_exist E P H hc hy) L.reach (fun r=> balance_cost E U L Z P H p q r n hc hy)
end YM.OPE.Arboreal
