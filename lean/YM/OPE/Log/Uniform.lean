import YM.OPE.Log.Scales
/-!
# Full requested elementary (non-nested) logarithmic bound under matrix ticket
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Metric Lattice RG Wilson
open scoped Topology BigOperators Classical ContDiff

-- usable when the requested overall geometry may include disparate scales
def badge (r:ℝ):= 1+run r
lemma uniform_wallet {V A : Type*}{g:ℝ→ V→Prop}{F:ℝ→ V→A} {T:ℝ→ V→ℝ}[Norm A] (ht:∀ (x:ℕ→ V)(r:ℕ→ℝ), Tendsto r atTop (𝓝[>] 0) → (∀ᶠ i in atTop,g (r i) (x i)) → Tendsto (fun i=> T (r i) (x i)) atTop atTop ∧ Wallet atTop (fun i=> T (r i) (x i)) (fun i=> F (r i) (x i))): ∃ p:ℕ, ∀ᶠ r:ℝ in 𝓝[>]0,∀ x:V,g r x → ‖F r x‖ ≤ T r x^p :=by
    by_contra! h
    have hf(i:ℕ):∃ r:ℝ,0<r∧r ≤ Real.exp (-i)∧ ∃ x:V,g r x ∧ T r x^i < ‖F r x‖:=by
       let l:Filter ℝ:= 𝓝[>]0; have hh:∃ᶠ r in l, ∃ x:V, g r x ∧ T r x^i < ‖F r x‖:=h i; obtain ⟨r,hr,hR,hx⟩:= (hh.and_eventually ((show ∀ᶠ i in l,0 < i from self_mem_nhdsWithin).and ((ge_mem_nhds (Real.exp_pos (- (i:ℝ)))).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨r,hR,hx,hr⟩
    choose r hr hR x hX hv using hf
    have he:Tendsto r atTop (𝓝 0):= squeeze_zero' (Eventually.of_forall fun i=> (hr i).le) (Eventually.of_forall hR) (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
    obtain ⟨hh,p,hp⟩:= ht x r (tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hr⟩) (Eventually.of_forall hX); obtain ⟨i,hf,hh,h⟩:= (hp.and ((eventually_ge_atTop p).and (hh.eventually_ge_atTop 1))).exists; exact (hv i).not_ge (hf.trans (pow_le_pow_right₀ h hh))

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} (U:Spec.Final C f S) {I J L:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    (p:I→ C.book.Token)(q:J→ C.book.Token) (n:ℕ) (h: Services C f S)
    {𝓕: Filter (ℕ×ℕ)}[𝓕.NeBot]{W r' D} (L': LogPackage C W r' D) (hM:𝓕 ≤ f.fuse)(hV:MatrixTicket (C:=C) S U.sector.derivatives 𝓕)
    {P:Prescription U.sector.derivatives}(hP:P.Coherent){l: Filter L}[l.NeBot]
    {M c η:ℝ} (hm:0≤ M)(hη:0<η)
local notation "ψ"=> 𝓝[>] (0:ℝ)
private lemma restore {a:ℝ}{w d k:ℕ}(v:ℝ)(h:0<v)(he:0 ≤ run v)(hz:v^d/v^w*a ≤ run v^k) : a ≤ badge v^k * (v^w/v^d) :=by
    have hx:run v^k ≤ badge v^k:= pow_le_pow_left₀ he (by unfold badge; linarith only) _
    refine (le_div_iff₀ (by exact div_pos (pow_pos h d) (pow_pos h w))).mpr (((mul_comm ..).le.trans hz).trans hx) |>.trans_eq ?_; rw [div_eq_mul_inv,inv_div]

include U h L' hM hV hP hm hη
lemma terms (w:Mode U.sector.derivatives): ∃ k:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀ x:I→ E4,∀ o:E4, WithinRoom r M η x o →
    (∀ u∈ (P.sheet w).support, Injective (beside (OPE.away x o) (bearing u))) ∧ ‖P.ope w x p o‖ ≤ badge r^k * (r^w.fst / r^sigma p):=by
    obtain ⟨k,hk⟩:=uniform_wallet (g:=fun r (x:(I→ E4)×E4)=>WithinRoom r M η x.1 x.2) (F:=fun r (x:(I→ E4)×E4)=>(r^sigma p/r^w.fst:ℝ) • P.ope w x.1 p x.2) (T:=fun r _=> run r) (fun x r hr hx=> ⟨run_towards hr, compensated_coeff (z:=fun i=>(x i).2) (x:=fun i=>(x i).1) U p h L' hM hV hP hr hm hη hx w⟩)
    refine ⟨k,?_⟩; filter_upwards [hk, (run_towards (r:=fun i=>i) tendsto_id).eventually_ge_atTop 0, small_coeff U hP h p hη hm zero_lt_one w, show ∀ᶠ i in ψ,0 < i from self_mem_nhdsWithin] with r hr' he hz hr x z hx; have hf := hr' (x,z) hx; refine ⟨(hz x z hx).1,restore _ hr he ?_⟩; simpa only [norm_smul,Real.norm_of_nonneg (div_pos (pow_pos hr (sigma p)) (pow_pos hr w.fst)).le] using hf
lemma horizons (hc: 0<c) : ∃ k:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀ (x:I→ E4)(y:J→ E4)(o:E4), WithinRoom r M η x o→ ClearOf o y c→ Injective (beside x y) ∧ Injective (beside (sole o) y) ∧
     Tested U P n x p o y q (badge r^k * (r^(n+1)/r^sigma p)):=by
    let V:= (I→ E4)× E4 × (J→ E4); obtain ⟨k,hk⟩:= uniform_wallet (g:=fun r (x:V)=> WithinRoom r M η x.1 x.2.1 ∧ ClearOf x.2.1 x.2.2 c) (F:=fun r (x:V)=>r^sigma p/r^(n+1)*‖groundError U P n x.1 p x.2.1 x.2.2 q‖) (T:=fun r _=> run r) (fun x r hr hx=> ⟨run_towards hr,ground_plus U p q n h L' hM hV hP hr hm hη (hx.mono fun i hi=> hi.1) hc (hx.mono fun i hi=> hi.2)⟩)
    refine ⟨k,?_⟩; filter_upwards [hk,(run_towards (r:=fun i=>i) tendsto_id).eventually_ge_atTop 0,small_horizon U hP h p q hη hm hc zero_lt_one n,show ∀ᶠ i in ψ,0 < i from self_mem_nhdsWithin] with r hx he hz hr x y z hX hY; obtain ⟨h₁,h₂,h₃⟩:= hz x z y hX hY; refine ⟨h₁,h₂, tested U P _ _ _ _ _ _ (restore r hr he ?_) h₁ h₂⟩; exact (Real.le_norm_self _).trans (hx (x,z,y) ⟨hX,hY⟩)
end YM.OPE.Log
