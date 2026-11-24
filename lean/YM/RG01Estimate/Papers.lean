import YM.RG01Estimate.RealTaylor
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Office
open Function Filter Set Metric MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Brush RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {A E F H : Type} [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
local notation "X" => ℝ × E
variable (f : A → ℝ × E → F) (s:Set A)(Z:Set E)

def held (x:X):A→F:= s.indicator (fun z=> f z x)

/-- Office finite radius on flow + read. Supplies at flat with the same cost.
These are *ordinary* kernel envelopes for analytic input even when the real evaluator
has splits. Need a field/gauge/mask license to use in the latter. No order exchange. -/
structure Roll (b C:ℝ) (j:ℕ) : Prop where
  occupied : ∀ i∈s,∀ x∈corridor b Z, Brush j C 1 (f i) x
  tested : ∀ x∈corridor b Z,StronglyMeasurable (held f s x)
section basic
variable {f s Z} {b c C D:ℝ} {j k n:ℕ}
variable (p : Roll f s Z b C j)
include p
lemma Roll.of_le (he : C≤D) (hv : c≤b) (hk : k≤j) : Roll f s Z c D k:= by
  have hs:corridor c Z⊆ corridor b Z:=Set.prod_mono (ball_subset_ball hv) (le_refl _)
  exact ⟨fun i hi x hx=> ((p.occupied i hi x (hs hx)).smaller hk).climb he le_rfl,fun x hx=> p.tested x (hs hx)⟩
lemma Roll.plus {g : A → X → F}(h : Roll g s Z b D j) : Roll (fun i x=>f i x+g i x) s Z b (C+D) j := by
  refine ⟨fun i hi x hx=> (p.occupied i hi x hx).gathering (h.occupied i hi x hx),fun x hx=>?_⟩
  rw [show held _ s x=(fun z=> held f s x z+held g s x z) from funext fun z=> by unfold held; by_cases hh:z∈s <;> simp [Set.indicator,hh] ]; exact (p.tested _ hx).add (h.tested _ hx)
lemma Roll.active {g : A→X→ℝ}(h : Roll g s Z b D j) : Roll (fun i x=> g i x • f i x) s Z b (D*C*3^j) j := by
  refine ⟨fun i hi x hx=>?_,fun x hx=>?_⟩
  · have hu:=h.occupied i hi x hx; have hv:=p.occupied i hi x hx
    rw [show (3:ℝ)=1+(1+1) by norm_num]
    exact ((hu.twins hv (ContinuousLinearMap.lsmul ℝ ℝ)).climb (mul_le_of_le_one_left (mul_nonneg hu.nonneg hv.nonneg) (ContinuousLinearMap.opNorm_lsmul_le ..)) le_rfl|>.trim)
  have ht:= (h.tested x hx).smul (p.tested x hx)
  rw [show held _ s x=(fun z=> held g s x z • held f s x z) from funext fun z=> by unfold held; by_cases h:z∈s <;> simp [Set.indicator,h] ]; exact ht
lemma Roll.cumulative (u : F→ H) (ht : Continuous u) (he : ∀ i∈s,∀ x∈corridor b Z, Brush j D 1 u (f i x)) (hs : MeasurableSet s): Roll (fun i => u ∘ f i) s Z b (clump j C D) j := by
   refine ⟨fun i hi x hx=> composite (p.occupied i hi x hx) (he i hi x hx),fun x hx=>?_⟩
   have hv:= (ht.comp_stronglyMeasurable (p.tested x hx)).indicator hs
   rwa [show s.indicator _ = held (fun i=> u ∘ f i) s x from funext fun z=> by unfold held; by_cases h:z∈ s <;> simp [Set.indicator,h] ] at hv
omit p

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

-- The test receipt doesn't demand a width cost for a shrinking fluctuation interval. Use measured limits at b=0.
lemma Roll.one (p:Roll f s Z b C (j+1)) (hp : IsOpen Z): Roll (fun i=> RealTaylor.drop (f i)) s Z b C j:= by
   let g (i:A): X→ F:=RealTaylor.drop (f i)
   have h : ∀ i∈s,∀ x∈corridor b Z, Brush j C 1 (g i) x:= fun i hi x hx=> pay_down (f i) Z b hp x hx (p.occupied i hi)
   refine ⟨h,?_⟩
   rintro ⟨q,y⟩ hx
   have hk : ‖q‖ < b:=mem_ball_zero_iff.mp hx.1; have hb:0<b:= (norm_nonneg _).trans_lt hk
   have hy : y∈ Z:= hx.2
   have h₀: (0,y) ∈ corridor b Z:= ⟨mem_ball_self hb,hy⟩
   have hX (t:ℝ)(ht:t∈ball (0:ℝ) b)(hT:t≠0): StronglyMeasurable (held g s (t,y)) := by
      let a: X:=(t,y); have ha : a∈ corridor b Z:= ⟨ht,hy⟩
      have he : held g s (t,y)= fun i=> t⁻¹ • (held f s (t,y) i-held f s (0,y) i) := by
        funext i; by_cases hi:i∈s
        · simp only [held,indicator_of_mem hi]; have hv:=layer (f i) a (fun t ht=> p.occupied i hi _ (inner_jet Z _ ha t ht))
          change f i (t,y)= _+ t • RealTaylor.drop (f i) (t,y) at hv; rw [hv,add_sub_cancel_left,inv_smul_smul₀ hT]
        simp only [held,indicator_of_notMem hi]; simp
      rw [he]; exact ((p.tested _ ha).sub (p.tested _ h₀)).const_smul _
   by_cases hT:q=0
   · subst q
     -- choose countable sequence of nonzero t inside collar
     obtain ⟨u,-,hu,H⟩:=exists_seq_strictMono_tendsto' (neg_lt_zero.mpr hb)
     have hU n:u n∈ ball (0:ℝ) b:= mem_ball_zero_iff.mpr (show |u n|< b from abs_lt.mpr ⟨(hu n).1,(hu n).2.trans hb⟩)
     refine stronglyMeasurable_of_tendsto (f:=fun n=> held g s (u n,y)) atTop (fun n=> hX _ (hU n) (hu n|>.2.ne)) ?_
     rw [tendsto_pi_nhds]; intro x
     by_cases ht:x∈s
     · simp only [held,indicator_of_mem ht]
       exact ((h x ht _ h₀).smooth.continuousAt).tendsto.comp (H.prodMk_nhds tendsto_const_nhds)
     simp only [held,indicator_of_notMem ht]; exact tendsto_const_nhds
   exact hX _ hx.1 hT
lemma Roll.further (p:Roll f s Z b C (j+n)) (hp:IsOpen Z) : Roll (fun i=> pages (f i) n) s Z b C j := by
  induction n generalizing j with
  | zero=>exact p
  | succ i ih=> exact (ih (j:=j+1) (by rw [show j+1+i=j+(i+1) by omega]; exact p)).one hp
end basic

section atlas
variable {f : A → ℝ × E → F}
variable {Z}
-- Large fluctuation radius, width allowed to shrink in the b-variable independently
-- for each radius. Only need at flat for replacing the truncation by full polynomial
-- gaussian integration. No off-axis or entire estimates beyond the stated boxes.
structure Atlas [NormedAddCommGroup A] (f : A → ℝ × E→ F) (Z : Set E) (k j:ℕ) (C:ℝ) : Prop where
  supply (t:ℝ) : 0 < t → ∃ v:ℝ, 0 < v ∧ Roll f (closedBall 0 t) Z v (C*(1+t)^k) j

variable {k n m l j : ℕ} {C D b:ℝ}
section read
variable [NormedAddCommGroup A] (p : Atlas f Z k j C)
include p
lemma Atlas.of_le (hk : k ≤n) (hj : l≤j)(he : C≤D)(hC : 0 ≤ C) : Atlas f Z n l D:= by
  refine ⟨fun t ht=>?_⟩; obtain ⟨v,hv,H⟩:=p.supply _ ht
  exact ⟨v,hv,H.of_le (by gcongr <;> linarith) le_rfl hj⟩
lemma Atlas.plus {g : A→X→F} (h:Atlas g Z n j D)(hC:0≤C)(hD:0≤D): Atlas (fun i x=>f i x+g i x) Z (k+n) j (C+D):= by
  constructor; intro t ht
  obtain ⟨v,hv,h⟩:= (h.of_le (Nat.le_add_left n k) le_rfl le_rfl hD).supply t ht
  obtain ⟨u,hu,h'⟩:= (p.of_le (k:=k) (Nat.le_add_right k n) le_rfl le_rfl hC).supply t ht
  refine ⟨min u v,lt_min hu hv,?_⟩; rw [add_mul]
  exact (h'.of_le le_rfl (min_le_left ..) le_rfl).plus (h.of_le le_rfl (min_le_right ..) le_rfl)
lemma Atlas.active {g:A→X→ℝ} (h: Atlas g Z n j D): Atlas (fun i x=>g i x • f i x) Z (n+k) j (D*C*3^j):= by
   constructor; intro t ht
   obtain ⟨a,ha,hg⟩:=h.supply t ht; obtain ⟨b,hb,hf⟩:=p.supply t ht
   refine ⟨min a b, lt_min ha hb,?_⟩
   apply ((hf.of_le le_rfl (min_le_right ..) le_rfl).active (hg.of_le le_rfl (min_le_left ..) le_rfl)).of_le _ le_rfl le_rfl
   exact le_of_eq (by rw [pow_add]; ring)
omit p
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma Atlas.further (p : Atlas f Z k (j+n) C) (hp:IsOpen Z): Atlas (fun i=> pages (f i) n) Z k j C := by
  constructor; intro t ht
  obtain ⟨v,hv,H⟩:= p.supply t ht
  exact ⟨v,hv,H.further hp⟩
-- Useful at all radii including zero. A shift by one pays the actual `Price`.
lemma Atlas.cost (p : Atlas f Z k (j+n) C) (hp:IsOpen Z) (i:A) (y:E) (hy:y∈Z):
    Brush j (C*(1+(‖i‖+1))^k) 1 (piece (f i) n) y := by
  let t:= ‖i‖+1; have h:0<t:= add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  obtain ⟨v,hv,H⟩:= p.supply t h
  exact priced_piece _ Z v hp y hy n hv (H.occupied i (mem_closedBall_zero_iff.mpr (le_add_of_nonneg_right zero_le_one)))
lemma Atlas.measured (p : Atlas f Z k (j+n) C) (hp:IsOpen Z) (y:E)(hy:y∈Z): StronglyMeasurable (fun i=> piece (f i) n y) := by
  let M z w:= (closedBall (0:A) ((z:ℕ)+1:ℝ)).indicator (fun i=> piece (f i) n y) w
  apply stronglyMeasurable_of_tendsto (f:=M) atTop
  · intro i; obtain ⟨v,hv,H⟩:= (p.further hp).supply (i+1:ℝ) (by positivity); exact H.tested (0,y) ⟨mem_ball_self hv,hy⟩
  rw [tendsto_pi_nhds]; intro x; apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x‖] with i hi
  unfold M; rw [indicator_of_mem (mem_closedBall_zero_iff.mpr (show ‖x‖≤ (i:ℝ)+1 from hi.trans (le_add_of_nonneg_right zero_le_one)))]
end read
end atlas
end YM.RG01Estimate.Office
