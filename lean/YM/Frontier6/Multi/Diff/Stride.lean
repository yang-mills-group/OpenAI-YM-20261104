import YM.Frontier6.Multi.Diff.Perturb

/-!
# Off-graph convergence; pick direction lines placing every axis on micro grids

Use distinct congruence classes for coordinates **across** all moving slot
profiles. Centers themselves need no relation to the micro grids.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Lattice
open scoped Topology BigOperators ContDiff Classical
variable {I V X:Type} [Fintype V][DecidableEq V]{T : Fareway I}
variable (S:Schedule)(x:V→ E4)(a:ℝ)(z:V × Axis) (k:ℕ)
set_option quotPrecheck false

-- The updates, called wag

def wag (t:ℝ) : V→ E4:= Function.update x z.1 (chord z.2 (x z.1) a t)
abbrev cadence (V:Type)[Fintype V]:ℝ:= Fintype.card V+1
abbrev avatar (v:V) : ℤ:= (Fintype.equivFin V v).val
def period (z:V × Axis):Prop := ∃ n:ℤ, x z.1 z.2=a*(avatar z.1+n*cadence V)
def swing (V:Type)[Fintype V](k:ℕ):ℝ:= cadence V*((2:ℝ)^k+2)
lemma swing_pos: 0 < swing V k:=by unfold swing cadence; positivity
lemma wag_eq (t:ℝ): wag x a z t z.1=chord z.2 (x z.1) a t:= update_self ..
lemma wag_untouched (i:V)(t:ℝ)(he:i≠z.1): wag x a z t i=x i:=update_of_ne he ..
lemma wag_zero : wag x a z 0=x:=by ext1 i; by_cases h:i=z.1; subst i; simp [wag_eq,chord,Ward.inc]; exact wag_untouched _ _ _ _ _ h
lemma wag_cont : Continuous (wag x a z):= by
    unfold wag; apply continuous_pi; intro i; by_cases h:i=z.1
    · subst i; simp only [update_self]; unfold chord Ward.inc; fun_prop
    simp only [update_of_ne h]; exact continuous_const
lemma wag_preserves (p:V × Axis)(h:p≠z) (t:ℝ) (hx:period x a p) : period (wag x a z t) a p:= by
   by_cases he : p.1=z.1
   · have hz:p.2≠z.2:=fun e=> h (Prod.ext he e); unfold period at hx ⊢; rw [he] at hx ⊢; simpa [wag_eq,chord,Ward.inc,hz] using hx
   unfold period; rw [wag_untouched _ _ _ _ _ he]; exact hx
lemma strideArced (ha:0<a):∃ q:Fin (2^k)→ℝ, arced k (swing V k) q ∧ ∀ j: Fin (2^k), period (wag x a z (q j)) a z:=by
   let b:= avatar z.1; let u:=x z.1 z.2 / a; let p:= cadence V; have hp':1 ≤ p:= by unfold p cadence; linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
   have hp:0<p:=one_pos.trans_le hp'; let v:=(u-b)/p; have hv:u=p*v+b:=by dsimp only [v]; field_simp; ring
   let w:= ⌊v⌋; have hw:(w:ℝ)≤v:=Int.floor_le _; have hz:v<w+1:=Int.lt_floor_add_one _
   let Q(j:Fin (2^k)):ℤ:=w+j.val+1; let q(j:Fin (2^k)):= (b:ℝ)+(Q j:ℝ)*p-u; refine ⟨q,⟨fun j=>?_,fun i j h=>?_⟩,fun j=> ⟨Q j,?_⟩⟩
   · have hh:(0:ℝ)≤ j.val:=by positivity
     have ht:(j.val:ℝ)<(2:ℝ)^k:=by exact_mod_cast j.isLt
     change -(p*((2:ℝ)^k+2)) ≤ q j ∧ q j≤ p*((2:ℝ)^k+2); unfold q; rw [hv]; unfold Q; push_cast; constructor
     · linarith only [mul_nonneg hh hp.le, mul_pos hp (show 0 < (2:ℝ)^k+2 from (by positivity)), mul_lt_mul_of_pos_right hz hp]
     nlinarith only [mul_le_mul_of_nonneg_right hw hp.le,mul_le_mul_of_nonneg_right ht.le hp.le,hp]
   · have hi:(i.val:ℝ) + 1 ≤ j.val:=by exact_mod_cast h
     unfold q Q; push_cast; linarith only [hp',mul_le_mul_of_nonneg_right hi hp.le]
   rw [wag_eq]; have hu:x z.1 z.2= u*a:=by unfold u; field_simp
   simp only [chord,Ward.inc,PiLp.add_apply,PiLp.smul_apply,basis_eq,if_true, smul_eq_mul,mul_one]; rw [hu]; change u*a+((b:ℝ)+(Q j:ℝ)*p-u)*a=a*((b:ℝ)+(Q j:ℝ)*p); ring
lemma period_to_cover {t:ℕ}(h:∀ i:V×Axis,period x (S.a t) i):∃ v:V→ Cover, x=(S.gridPoint t) ∘ v:=by
    choose p hp using h; let y(i:V)(b:Axis):ℤ:= avatar i+p (i,b)*(Fintype.card V+1:ℕ); refine ⟨y,?_⟩; ext i b; dsimp only [comp_apply,Schedule.gridPoint]; unfold y; push_cast; exact hp (i,b)
lemma period_injective (hx:∀ i:V×Axis,period x a i)(he:0<a)(b:Axis):Injective (fun v:V=>x v b):=by
    intro i j h; obtain ⟨m,hm⟩:= hx (i,b); obtain ⟨n,hn⟩:= hx (j,b); let N:= Fintype.card V+1; let A(k:V):ℤ:= avatar k; have hv'(k:V): A k < N:=by dsimp only [A,avatar]; exact_mod_cast lt_trans (Fintype.equivFin V k).isLt (show Fintype.card V < N from Nat.lt_add_one _)
    have hN(k:V):0 ≤ A k:=Int.natCast_nonneg ..; have he':A i+m*N=A j+n*N:=by
       apply Int.cast_injective (α:=ℝ); push_cast; have hf : (N:ℝ)=cadence V:=by unfold N cadence; push_cast; rfl
       rw [hf]; exact mul_left_cancel₀ he.ne' (hm.symm.trans (h.trans hn))
    apply (Fintype.equivFin V).injective; apply Fin.ext
    suffices A i=A j by unfold A avatar at this; exact_mod_cast this
    have ht: ((A i+m*N) % N)=A i:=by rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (hN i) (hv' i)]; -- test
    rw [←ht,he',Int.add_mul_emod_self_right, Int.emod_eq_of_lt (hN j) (hv' j)]; -- test
-- Cost of walk, including interpolation rails
lemma wag_neighbors {a x':I→ℝ}{x:I→V→E4}{p:ℝ}(h:T.Costs a (-p))(he:T.Costs x' 0) : Neighbors T x (fun i=> wag (x i) (a i) z (x' i)) p:= by
   intro i; by_cases ht:i=z.1
   · subst i; simp_rw [wag_eq, chord, Ward.inc, add_sub_cancel_left]; exact (show 0+-p+0= -p from by ring) ▸ (Fareway.Costs.const _ |>.scalarR₀ (he.mul h))
   simp_rw [wag_untouched _ _ _ _ _ ht, sub_self]; exact Costs.free
end YM.Frontier6.Road
