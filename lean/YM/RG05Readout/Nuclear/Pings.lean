import YM.RG05Readout.Nuclear.Beads
/-! Uniform over dyadic-gird neighborhoods. Keep exponent EXACT for all
 dimension losses at full Taylor demand. Occupancy of both coarse/refined
 offsets here does not depend on chart radius, including Hermite correction.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
set_option quotPrecheck false
-- unit mesh in all directions. Includes count-zero for empty test points
lemma piece_count {D:Finset (V→Cover)} (r:ℝ)(hr:0<r) (N:ℕ)(x:U)(h:∀ y∈D,‖clue r ∘ y-x‖≤r*N) : D.card ≤ (plot V (2*N)).card:=by
    rcases Finset.eq_empty_or_nonempty D with hv|⟨i,hi⟩
    · simp [hv]
    let f := fun j: V→Cover=>j-i; have ht:D.image f⊆ plot V (2*N):=by
       intro z hz; obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hz; apply Fintype.mem_piFinset.mpr; intro a; apply Fintype.mem_piFinset.mpr; intro k; change j a k-i a k∈ room _; apply Finset.mem_Icc.mpr
       let u:= clue r ∘ j; let v:= clue r ∘ i; have hu:= (h j hj); have he:= h i hi
       have hg : ‖u-v‖≤ r*N+r*N:= (norm_sub_le_norm_sub_add_norm_sub u x v).trans (add_le_add hu ((norm_sub_rev x v).le.trans he))
       have hl:|r*((j a k:ℝ)-(i a k:ℝ))|≤ r*N+r*N:= by
           rw [mul_sub]; refine le_trans (b:=‖(u-v) a‖) ?_ ((norm_le_pi_norm (u-v) a).trans hg); exact PiLp.norm_apply_le ((u-v) a) k
       rw [abs_mul,abs_of_nonneg hr.le,← mul_add] at hl; have hf:= abs_le.mp (le_of_mul_le_mul_left hl hr); constructor
       · exact_mod_cast (show -(↑(2*N):ℝ) ≤ (j a k:ℝ)-(i a k:ℝ) by push_cast; linarith only [hf.1])
       exact_mod_cast (show (j a k:ℝ)-(i a k:ℝ) ≤ (2*N:ℕ) by push_cast; linarith only [hf.2])
    exact (Finset.card_image_of_injective _ (show Injective f from sub_left_injective)).ge.trans (Finset.card_le_card ht)
-- cost receipts.Pow-r ladder.One mark valuations interpreted Cap
abbrev Tall (f:Complexion E)(s:ℕ)(R e:ℝ):Prop:=∀ i ≤ s,∀ x, ‖iteratedFDeriv ℝ i f.val x‖ ≤ R^i*e
lemma uniform_C (x:Body) (h:IsCompact (tsupport x.val)) (s:ℕ) : ∃ C>0, Tall (E:=E4) x s 1 C:=by
    have he (i:Fin (s+1)): ∃ c:ℝ,0≤ c ∧ ∀ z,‖iteratedFDeriv ℝ i.val x.val z‖≤ c:=by
       obtain ⟨c,hc⟩:= h.exists_bound_of_continuousOn (body_smooth x i.val|>.continuous_iteratedFDeriv (m:=i.val) le_rfl|>.continuousOn)
       refine ⟨max 0 c, le_max_left .., fun z=>?_⟩; by_cases hz:z∈ tsupport x.val; exact (hc z hz).trans (le_max_right ..); rw [show iteratedFDeriv ℝ i.val x.val z=0 from notMem_support.mp (fun h=> hz (support_iteratedFDeriv_subset i.val h)),norm_zero]; exact le_max_left ..
    choose C hC hh using he; refine ⟨1+∑ i,C i, add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _=> hC i),fun i hi z=> ?_⟩
    rw [one_pow,one_mul]; exact le_trans (hh ⟨i,(by omega)⟩ z) ((Finset.single_le_sum (fun i _=> hC i) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))
lemma collar{f g:Complexion E} : tsupport (chord f g).val ⊆ tsupport f.val∩tsupport g.val:=by
    have he:support (chord f g).val=support f.val∩support g.val:=support_mul f.val _; rw [tsupport,he];exact closure_inter_subset ..
lemma hood_compact:IsCompact (tsupport Hood.val):=(isCompact_closedBall (0:E4) 2).of_isClosed_subset isClosed_closure fun x hx=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hood_live x hx)
lemma hood_strong (a:Body):IsCompact (tsupport (chord Hood a).val):= hood_compact.of_isClosed_subset isClosed_closure fun _ h=> (collar h).1
noncomputable def bond (u:Body)(k:ℕ):ℝ:=(uniform_C (chord Hood u) (hood_strong _) k).choose
noncomputable def rung (k:ℕ):ℝ:=(uniform_C Hood hood_compact k).choose
lemma bond_pos (u:Body)(k:ℕ):0<bond u k:=(uniform_C (chord Hood u) (hood_strong _) k).choose_spec.1
lemma rung_pos (k:ℕ):0<rung k:=(uniform_C Hood hood_compact k).choose_spec.1
lemma Tpatch (x:E4)(f:Body)(c r:ℝ)(hr:0<r) {d:ℕ}(h:Tall (E:=E4) f d 1 c): Tall (E:=E4) (patchShift x r f) d r⁻¹ c:=by
     intro i hi z; unfold patchShift; rw [Native.pulled,norm_smul,Real.norm_of_nonneg (by positivity)]; apply mul_le_mul_of_nonneg_left _ (by positivity); specialize h i hi (-r⁻¹ • x+r⁻¹ • z); simp only [one_pow,one_mul] at h; exact h
lemma Tiepatch (x:E4)(f:Body)(r:ℝ)(hr:0<r) (d:ℕ): Tall (E:=E4) (chord (pebble r x) (patchShift x r f)) d r⁻¹ (bond f d):= Tpatch x (chord Hood f) (bond f d) r hr ((uniform_C _ (hood_strong _) d).choose_spec.2)
lemma threshold {f g:Complexion E}{d:ℕ} (u v:ℝ){a:ℝ}(h:Tall f d u a)(ht:Tall g d u v)(ha:0≤a)(hb:0 ≤ v)(hu:0≤u): Tall (E:=E) (chord f g) d u (2^d*a*v):=by
    intro i hi x; apply (norm_iteratedFDeriv_mul_le (lit f d) (lit g d) x (Nat.cast_le.mpr hi)).trans; apply le_trans (Finset.sum_le_sum fun j (hj:j∈ Finset.range (i+1)) =>mul_le_mul (mul_le_mul_of_nonneg_left (h j (by have := Finset.mem_range.mp hj; omega) x) (Nat.cast_nonneg _)) (ht _ (by omega) x) (norm_nonneg _) (by positivity))
    let l:= Finset.range (i+1); have hf : (∑ j∈ l, (i.choose j:ℝ))= 2^i:=by exact_mod_cast Nat.sum_range_choose i
    calc
       _ = (∑ j∈ l, (i.choose j:ℝ))*(u^i*a*v) :=by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [show u^i=u^j*u^(i-j) by rw [← pow_add,show j+(i-j)=i from Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]]; ring
       _ ≤ _:= by rw [hf]; exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hi) (by positivity)).trans_eq (by ring)
-- single patch and replacement charge.Power attenuation
lemma patch_cap (s:ℕ)(x:E4)(f:Body)(r:ℝ)(hr:0<r)(h: r ≤ 1): Cap s (chord (pebble r x) (patchShift x r f)) (r⁻¹^s*bond f s):=fun _ hi y _=> (Tiepatch x f r hr s _ hi y).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_inv₀ hr |>.mpr h) hi) (bond_pos f _).le)
noncomputable def inter (X Y:E4)(r t:ℝ)(v:Body):Body := chord (pebble r X) (chord (pebble t Y) (patchShift X r v))
noncomputable def latch (v:Body)(s:ℕ):ℝ:=(2:ℝ)^s*((2:ℝ)^s*rung s*bond v s)
lemma latch_pos (v:Body)(s:ℕ):0 < latch v s:=by unfold latch; have :=bond_pos v s; have := rung_pos s; positivity
lemma fuel (s:ℕ)(x y:E4)(r t:ℝ)(v:Body)(hr:0<r)(ht:0<t)(hp:r ≤ 2*t)(hw:t≤r):Tall (E:=E4) (inter x y r t v) s r⁻¹ (latch v s):=by
    have hf:= Tiepatch x v r hr s; let A:=chord (pebble r x) (patchShift x r v)
    have hb:Tall (E:=E4) (pebble t y) s t⁻¹ (rung s):= Tpatch y Hood (rung s) t ht (uniform_C Hood hood_compact s|>.choose_spec.2); have hp':Tall (E:=E4) A s t⁻¹ (bond v s):=fun i hi z=> (hf i hi z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (inv_anti₀ ht hw) _) (bond_pos ..).le)
    intro i hi z; have he: inter x y r t v=chord (pebble t y) A:=Subtype.ext <| funext fun z=> mul_left_comm ((pebble r x).val z) _ _
    rw [he]; apply le_trans (threshold t⁻¹ _ hb hp' (rung_pos s).le (bond_pos ..).le (inv_pos.mpr ht).le i hi z)
    let T:=2^s*rung s*bond v s
    have hQ: t⁻¹ ≤ 2 *r⁻¹:=by rw [inv_le_iff_one_le_mul₀ ht,← div_eq_mul_inv]; field_simp; linarith
    have hTP: t⁻¹^i ≤ r⁻¹^i*(2:ℝ)^s:=by
          calc
             _ ≤ (2*r⁻¹)^i:=pow_le_pow_left₀ (inv_pos.mpr ht).le hQ _
             _ ≤ _:=by rw [mul_comm 2,mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hi) (by positivity)
    have hy:T≥ 0:=by unfold T; have := rung_pos s; have := bond_pos v s; positivity
    exact (mul_le_mul_of_nonneg_right hTP hy).trans_eq (by unfold latch T; ring)
lemma toll (s:ℕ)(x y:E4)(r t:ℝ)(v:Body)(hr:0<r)(hu:r ≤ 1)(ht:0<t)(hp:r ≤ 2*t)(hw:t≤r): Cap s (inter x y r t v) (r⁻¹^s*latch v s):=fun i hi z _=> (fuel s x y r t v hr ht hp hw i hi z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_inv₀ hr|>.mpr hu) hi) (latch_pos ..).le)
-- normalize receipts here
lemma smul_caps (a:ℂ){φ:Body}{s:ℕ}{c:ℝ}(hp:Cap s φ c): Cap s (a • φ) (‖a‖*c):= by
    intro i hi z hz; rw [SetLike.val_smul, iteratedFDeriv_const_smul_apply (body_smooth ..|>.contDiffAt),norm_smul];exact mul_le_mul_of_nonneg_left (hp i hi z hz) (norm_nonneg _)
end YM.RG05Readout.Nuclear
