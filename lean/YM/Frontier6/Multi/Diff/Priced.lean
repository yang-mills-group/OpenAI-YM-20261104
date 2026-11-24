import YM.Frontier6.Multi.Diff.Steer

/- smooth interpolation for all prices below a. Land on coordinate grids
   returning guard-free Cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}{T : Fareway I}{a b r:ℝ}
set_option quotPrecheck false
variable (K: Final C F S) (hG: Org.Grill C F) {x:I→ V→ E4}{s:I→ℝ} (v:V→ S.Tag)(c:I→ E4)(p:V × Axis)(d:ℕ)
lemma Aspect.turntight (he:Aspect T x)(hr:0 < r) : ∀ᶠ i in T.via, snug (c i) r (fun j=> x i j+c i):=by
   filter_upwards [ eventually_all.mpr fun i:V=>(he.1 i).from_allowance (T.minted_c (r/2) (half_pos hr)) (by norm_num), he.alive] with i hi hh; exact ⟨fun _ _ h=> hh (add_right_cancel h), fun j=> by simpa only [add_sub_cancel_right] using ((hi j).trans_lt (half_lt_self hr))⟩
lemma Aspect.cozy (he:Aspect T x) (hr:0 < r): ∀ᶠ i in T.via,snug 0 r (x i):=by simpa only [Pi.zero_apply, add_zero] using he.turntight 0 hr
lemma Aspect.stepW {r:ℝ}{L:I→ Icc (-r) r}(h:Aspect T x)(hx:T.Costs s (-a))(ha:1 < a): Aspect T (fun i=> wag (x i) (s i) p (L i)):= h.peal (wag_neighbors p hx (Costs.unlimited r (Eventually.of_forall fun i=>abs_le.mpr ((L i).property)))) ha
lemma Aspect.cozyInto (h:Aspect T x) (hp:T.Costs s (-a))(he:1<a)(z:ℝ)(hr:0<r): ∀ᶠ i in T.via,∀ t∈ Icc (-z) z,snug 0 r (wag (x i) (s i) p t):= by
    filter_upwards [eventually_uniform (P:=fun i (t:Icc (-z) z)=> snug 0 r (wag (x i) (s i) p t)) (fun t:I→ Icc (-z) z=> (h.stepW p (L:=t) hp he).cozy hr)] with i hi t h using hi (⟨t,h⟩ : Icc (-z) z)
lemma unlit_anchor (h:Aspect T x) (t:V→S.Tag) (hG:Org.Grill C F): T.Costs (fun i=> absorb K 0 d (assembly S (x i) t)) (wages t+havens K d):= by simpa only [add_zero] using! unlit K hG d h t (fun i=>0)
-- cost along tilted path s with any nonempty width
include hG
lemma bus (h:Aspect T x)(hx:T.Mint s (-a))(ha:1<a) (k:ℕ)(L:I→ Icc (-r) r): T.Costs (fun i=> drivers K v (x i) p 0 d k (s i) (L i)) (wages v+havens K d - (a-1)*k):=by
   let Z(i:I):= wag (x i) (s i) p (L i); have he:Aspect T Z:= h.stepW p hx.pay ha
   let t:= route K v p k; have hu:wages t= wages v+k:= revolve_cap K v p k
   have hp:= (unlit_anchor K d he t hG).scalarR₀ (hx.power k|>.pay); rw [hu, show -a*(k:ℝ)+(wages v+k+havens K d)= wages v+havens K d - (a-1)*k from (by ring)] at hp; exact hp
lemma shunned {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](F0:S.Field d→L[ℝ] X) (h:Aspect T x)(hx:T.Mint s (-a))(ha:1<a) : Guard T x s a (fun _ x=> F0 (absorb K 0 d (assembly S x v))) b:=by
    intro y hy p; have he:= h.peal hy ha
    obtain ⟨k,hk⟩:= exists_nat_gt ((wages v+havens K d - b)/(a-1))
    let U(n i t):= F0 (drivers K v (y n) p 0 d i (s n) t)
    have hl (x:I→Icc (-swing V k) (swing V k)): T.Costs (fun i=>U i k (x i)) _:= (bus K hG v p d he hx ha k x).mapped F0
    obtain ⟨r,hr,hV⟩:= Frontier6.Safe.limits K d
    refine ⟨k, U,?_⟩; filter_upwards [he.cozyInto p hx.pay ha (swing V k) hr, eventually_uniform (P:=fun i (u:Icc (-swing V k) (swing V k))=>‖U i k u‖ ≤ Real.exp (T.scale i*b)) fun u:I→Icc (-swing V k) (swing V k)=> hl u b (by linarith only [(div_lt_iff₀ (sub_pos.mpr ha)).mp hk])] with i hi hp
    refine ⟨funext fun z=>?_, fun j hj y' hy' => F0.hasFDerivAt.comp_hasDerivAt y' (driving K _ _ _ _ _ _ hV _ y' (hi y' hy')), fun z hz=>hp ⟨z,hz⟩⟩; simp only [U,drivers,pow_zero,one_smul,route_zero]

end YM.Frontier6.Road
