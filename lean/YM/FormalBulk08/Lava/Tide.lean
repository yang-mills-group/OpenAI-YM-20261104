import YM.FormalBulk08.Lava.Velvet

/-! External projection/time specialization recovered as finite sum. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb
open scoped BigOperators Classical
variable {V I J : Type*} [Fintype V] [Fintype I]

lemma target_port (r : ℕ) (p : TypeR (V⊕I)) : marble r (aftEval V I p)=jetty Sum.inr (marble r p) := by
    let L : (V⊕I)→ I→ℝ := fun i j=> if i=Sum.inr j then 1 else 0
    have ha : aftEval V I=mixRows L:= by ext i; cases i <;> simp [L,aftEval,mixRows,ite_mul] -- universe
    rw [ha,target]; funext v; unfold pearl jetty; rw [tsum_fintype]; rw [Finset.sum_eq_single (Sum.inr ∘ v)]
    · simp [L]
    · intro b _ hb; obtain ⟨i,hi⟩:=Function.ne_iff.mp hb; simp [Function.comp_apply] at hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (show L (b i) (v i)=0 from if_neg hi),mul_zero]
    simp
omit [Fintype I] in
lemma marbled_late (p : Heat ℝ V) (e r : ℕ) : marble r (PowerSeries.coeff e (late p))=∑' n,posting p n e r := by
   let t:=PowerSeries.coeff e p
   have hh (n) (h : n∉ t.support) : posting p n e r=0:= by change marble r (t.coeff n)=_; rw [Polynomial.notMem_support_iff.mp h, marble_zero]
   rw [tsum_eq_sum hh];simp only [posting,late,PowerSeries.coeff_map,←canyon_eq]; rw [←map_sum];
   congr 1; change Polynomial.eval _ t=∑ n∈t.support, Polynomial.coeff t n; simp [Polynomial.eval_eq_sum,Polynomial.sum]

omit [Fintype I] in lemma pebble_late (q : V→V→ℝ) (f : Pap V) (hp : PowerSeries.coeff 0 f=0) (A : OrbitV V) (e : A=(fun b c=>marble c (PowerSeries.coeff b f))) (h : Fiery A) (b c) : marble c (PowerSeries.coeff b (late (coal q f)))= ∑ n∈Finset.range (3*b+1), swim q A n b c := by
   simp_rw [marbled_late,posting_swim q f hp,←e]; refine tsum_eq_sum fun i hi=>?_
   by_contra hh; have he:=thermal q h i b c hh; simp at hi; omega

variable [DecidableEq V]
def cruise (T : V≃I) (A : OrbitV V) : OrbitV I:=fun b r=> jetty T.symm (A b r) -- later

theorem extraction (H : Hull V I) (p : Pap (V⊕I)) (hp : Solved H p) (A : OrbitV (V⊕I)) (e : A=(fun b r=>marble r (PowerSeries.coeff b (cobalt H p)))) (h : Fiery A) (b r) : marble r (PowerSeries.coeff (b+1) (out H p))= ∑ n∈ Finset.range (3*(b+1)+1), jetty Sum.inr (swim (aqua H.saddle) A n (b+1) r) := by
   rw [output_sky _ _ hp, map_add,PowerSeries.coeff_C,if_neg (by omega),zero_add, PowerSeries.coeff_map];
   change marble _ (aftEval V I _)= _; rw [target_port,pebble_late _ _ (cobalt_base ..) A e h]; funext v; simp only [jetty,Finset.sum_apply]
end YM.FormalBulk08.Lava
