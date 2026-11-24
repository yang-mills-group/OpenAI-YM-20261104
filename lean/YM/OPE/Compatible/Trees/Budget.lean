import YM.OPE.Compatible.Trees.Nest

/-!
# Costs in the units of the nested OPE estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[PartialOrder V][OrderBot V][Fintype V](E:Origin V)
    {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
    {l:Type}{φ:Filter l} {T:l→ℝ} {t:V→ℝ}{s:l→ V→ ℝ}{X:l→ V→ E4}
    {M η c:ℝ}(L:Layer E φ T M η t s X)
    (p:V→ S.Tag)(D:V→ℕ)
lemma portion_expanded (P:Finset V)(v:V) : portion E P v p=∑ i∈ glen E P v,(p i).1:=
  Finset.sum_coe_sort _ (fun i:V => (p i).1)
lemma payload_expanded (P:Finset V) : payload E P p t= ∑ i∈ brim E P, ((p i).1:ℝ)*t (par E i) :=
  Finset.sum_coe_sort _ (fun i:V => ((p i).1:ℝ)*t (par E i))

lemma payload_len (P:Finset V)(H:Crown P) (t:V→ℝ) : payload E P p t =
    (portion E P ⊥ p:ℝ)*t ⊥ + ∑ v∈ rest P, (portion E P v p:ℝ)*jump E t v := by
  let A (i:V):ℝ := (p i).1
  rw [payload_expanded]
  simp_rw [portion_expanded,Nat.cast_sum, Finset.sum_mul, glen,Finset.sum_filter]; simp only [bot_le,↓reduceIte]
  rw [Finset.sum_comm (t:=brim E P) (s:=rest P),← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
  intro i hi
  change A i * t (par E i) = A i*t ⊥ + ∑ v ∈ rest P, if v ≤ i then A i*jump E t v else 0
  have h := (on_brim E P).mp hi
  calc A i*t (par E i)= A i*(t ⊥+∑ v∈ trail P (par E i),jump E t v) := congr_arg _ (path_sum E H _ h.2.2 t).symm
       _ = _ := by
        rw [mul_add, Finset.mul_sum,trail,Finset.sum_filter]; congr 1
        refine Finset.sum_congr rfl fun b hb=> ?_
        have he : b ≤ par E i ↔ b ≤ i := ⟨fun g=> g.trans (par_le ..),fun g => touch_par E
          (lt_of_le_of_ne g (fun e=> h.1 (e ▸ (Finset.mem_erase.mp hb).2)))⟩
        simp only [he]

/-- Total power-loss budget at the actual collapsing radii. `path_sum`
at a frontier input gave the proof of this accounting, not an estimate
that assumed ratios controlled by one mesh. -/
def fuel (p:V→ S.Tag) (ε k:ℝ)(s:V→ℝ):ℝ := (s ⊥)^(k-(portion E (heart V) ⊥ p:ℝ)-ε)*
  ∏ v∈ rest (heart V), (rat E s v)^(-(portion E (heart V) v p:ℝ)-ε)
def plugs (s:V→ℝ):ℝ := ∑ v∈ rest (heart V), (rat E s v)^(D v+1)
lemma rate_product {I:Type}(A:Finset I)(s:I→ℝ)(f:I→ l→ℝ)(h:Tendsto T φ atTop)
    (hp:∀ i∈ A,RateIs φ T (f i) (s i)) : RateIs φ T (fun i=> ∏ v∈ A,f v i) (∑ v∈A,s v) := by
  induction A using Finset.induction_on with
  | empty => simpa using (RateIs.const h zero_lt_one)
  | insert i A hi ih => simp_rw [Finset.prod_insert hi,Finset.sum_insert hi]; exact
      (hp i (Finset.mem_insert_self ..)).mul (ih fun j hj=> hp j (Finset.mem_insert_of_mem hj))

include L
lemma fuel_rate (ε k:ℝ) : RateIs φ T (fun i => fuel E p ε k (s i)) (demand E (heart V) p t k+ε) := by
  let A := portion E (heart V) ⊥ p
  let f (v:V):ℝ := -(portion E (heart V) v p:ℝ)-ε
  have hw := ((L.prices _ L.canopy).rpow (k-(A:ℝ)-ε)).mul
    (rate_product (rest (heart V)) (fun v=> f v*(-jump E t v)) (fun v i=> (rat E (s i) v)^f v) L.flow
      (fun v hv=> (L.jump_rate E hv).rpow (f v)))
  refine hw.swap ?_
  unfold demand; rw [payload_len E p (heart V) (tall L.canopy)]
  have h v : f v*(-jump E t v)= (portion E (heart V) v p:ℝ)*jump E t v+ε*jump E t v:= by dsimp [f]; ring
  simp_rw [h,Finset.sum_add_distrib, ← Finset.mul_sum]
  have he : (∑ v∈ rest (heart V),jump E t v)= 1-t ⊥:= eq_sub_of_add_eq' L.charged
  rw [he]; dsimp only [A]; ring

variable [φ.NeBot] (Z : Services C F S) {ε:ℝ} (hε:0<ε) (a:Tones U)
include U hε Z
lemma coeff_price : ∀ᶠ i in φ, ‖frontierCoefficient E U (heart V) a (s i) (X i) p‖ ≤ fuel E p ε a.fst (s i) :=
    (fuel_rate E L p ε a.fst).outweigh (direct_cost E U L Z _ (tall L.canopy) p a)
      (lt_add_of_pos_right _ hε) L.flow
lemma seen_price {J:Type} [Fintype J] {Y:l→ J→ E4}(q:J→ S.Tag)(n:ℕ)(hc:0<c) (hy:∀ᶠ i in φ, ClearOf (X i ⊥) (Y i) c) :
    ∀ᶠ i in φ, Seen U n (s i ⊥) (picked (brim E (heart V)) (X i)) (picked (brim E (heart V)) p)
      (X i ⊥) (Y i) q (fuel E p ε (n+1:ℝ) (s i)) := by
  let H := tall L.canopy
  filter_upwards [L.live_bot E _ H S,L.words_exist E _ H hc hy, (fuel_rate E L p ε (n+1:ℝ)).outweigh
    (drift_cost E U L Z _ H p q n hc hy) (lt_add_of_pos_right _ hε) L.flow] with i he hi h using
      ⟨he,hi.1,hi.2,h⟩
lemma nested_price : ∀ᶠ i in φ, ‖frontierCoefficient E U (heart V) a (s i) (X i) p - nests E U D (heart V) a (s i) (X i) p‖ ≤
    fuel E p ε a.fst (s i)*plugs E D (s i) := by
  let B:= rest (heart V)
  by_cases h:B.Nonempty
  · let d (v:V):ℝ := (D v+1:ℝ)*jump E t v
    obtain ⟨v,hv⟩ := Finset.exists_minimalFor d B h
    have hh := hv.1; let γ := d v
    have hg : 0 ≤ γ := mul_nonneg (by positivity) (sub_nonneg.mpr
      (L.order E (Finset.mem_erase.mp hh).2 (par_le ..)))
    have hm := nests_cost E U L Z D (heart V) (tall L.canopy) a p hg (fun w hx=> by
      by_contra! hs; exact hs.not_ge (hv.2 hx hs.le))
    have hw := fuel_rate E L p ε a.fst
    have hf : RateIs φ T (fun i=> (rat E (s i) v)^(D v+1)) (-γ) := by
      apply ((L.jump_rate E hh).power (D v+1)).swap
      dsimp only [γ,d]; rw [Nat.cast_add_one,mul_neg]
    filter_upwards [(hw.mul hf).outweigh hm (by linarith only [hε]) L.flow, hw.pos,L.stays]
      with i hi hx ht
    exact le_trans hi (mul_le_mul_of_nonneg_left (Finset.single_le_sum (s:=B) (f:=fun v=> (rat E (s i) v)^(D v+1))
      (fun v g=> pow_nonneg ((ht.ratios E g).1).le _) hh) hx.le)
  filter_upwards with i
  unfold plugs
  rw [nests,dif_neg h,sub_self,norm_zero, Finset.sum_eq_zero (fun v g=> False.elim (h ⟨v,g⟩)), mul_zero]
end YM.OPE.Arboreal
