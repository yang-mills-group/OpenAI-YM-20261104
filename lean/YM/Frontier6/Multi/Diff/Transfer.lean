import YM.Frontier6.Multi.Diff.Stride
/-!
# along Fareways

With vector-valued targets. Compact topology only used for stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Lattice
open scoped Topology BigOperators ContDiff Classical
variable {I V:Type} [Fintype V][DecidableEq V]{T : Fareway I}
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
lemma teaser {k:ℕ}{p:ℝ}(hp:0<p) : ∃ A:ℝ,0<A∧∀ (f:ℕ→ℝ→X)(ε:ℝ)(x: Fin (2^k)→ℝ),0<ε →arced k p x→ (∀ w, ‖f 0 (x w)‖ ≤ ε)→ (∀ i<k,∀ y∈ Icc (-p) p, HasDerivAt (f i) (f (i+1) y) y)→ (∀ y∈Icc (-p) p,‖f k y‖ ≤ ε) → ∀ y∈ Icc (-p) p,‖f 0 y‖ ≤ ε*A:=by
    obtain ⟨A,hA,H⟩:= amph k p hp; refine ⟨A,hA,fun f ε x hε hx hW hh hf z hz=>?_⟩
    obtain ⟨L,hL,hE⟩:= exists_dual_vector'' ℝ (f 0 z); let Y (k:ℕ)(i:ℝ):= L (f k i)
    have hl(k:ℕ)(i:ℝ):‖Y k i‖ ≤ ‖f k i‖:=(L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hL)
    have hp:= H Y ε x hε hx (fun w=> (hl 0 _).trans (hW w)) (fun i hi y hy=> L.hasFDerivAt.comp_hasDerivAt y (hh i hi y hy)) (fun y hy=>(hl _ y).trans (hf y hy)) z hz
    unfold Y at hp; simpa only [show L (f 0 z)=‖f 0 z‖ from hE,Real.norm_of_nonneg (norm_nonneg _)] using hp
variable {x:I→V→ E4}{s:I→ℝ}{a b:ℝ}{f:I→(V→ E4)→X}
lemma eventually_uniform {l:Filter I}{J:Type*}{P:I→ J→ Prop}(h:∀ p:I→ J,∀ᶠ i in l,P i (p i)):∀ᶠ i in l,∀ j,P i j:=by
   cases isEmpty_or_nonempty J with
   | inl he=> exact Eventually.of_forall fun _=> isEmptyElim
   | inr he=> let p(i:I):= if h:∃ j,¬ P i j then h.choose else Classical.choice he; filter_upwards [h p] with i hi j; by_contra hz; have hp:∃ j,¬ P i j:= ⟨j,hz⟩; unfold p at hi; rw [dif_pos hp] at hi; exact hp.choose_spec hi
namespace Fareway.Costs
lemma stencilW {k:ℕ}{p:ℝ}{x:I→Fin (2^k)→ℝ}(hp:0<p)(hx:∀ i,arced k p (x i)){f:I→ℕ→ℝ→X} (he:∀ w:Fin (2^k),T.Costs (fun i=> f i 0 (x i w)) a) (hD:∀ᶠ i in T.via,∀ k'<k,∀ y∈ Icc (-p) p, HasDerivAt (f i k') (f i (k'+1) y) y)(hy:∀ y:I→ Icc (-p) p,T.Costs (fun i=> f i k (y i)) a): T.Costs (fun i=> f i 0 0) a:=by
    obtain ⟨A,hA,H⟩:=teaser (X:=X) (k:=k) hp; intro b hb; obtain ⟨c,hc,hc'⟩:=exists_between hb; let V i:= Real.exp (T.scale i*c)
    filter_upwards [eventually_all.mpr (fun i=> he i c hc),hD,Fareway.Costs.uniform (v:=fun i (p':Icc (-p) p)=> f i k p') hy hc,(T.minted c|>.mul (T.minted_c _ hA)).cheaper (T.minted b) (by linarith)] with i hh he hv hp'
    exact (H (f i) (V i) (x i) (Real.exp_pos _) (hx i) hh he (fun y hy=>hv (⟨y,hy⟩: Icc (-p) p)) 0 ⟨by linarith only [hp],hp.le⟩).trans hp'.le
end Fareway.Costs
-- Interpolation black box. n not fixed if thresholds vary across curves;
-- axis stencils frozen once per |curve|/cost exponent.
def Guard (T: Fareway I)(x:I→V→ E4)(s:I→ℝ)(a:ℝ)(f:I→ (V→ E4)→X)(b:ℝ):Prop:=
    ∀ y:I→V→ E4,Neighbors T x y a→∀ j:V × Axis,
    ∃ (n:ℕ)(g:I→ℕ→ℝ→X), ∀ᶠ i in T.via,g i 0=(fun z=> f i (wag (y i) (s i) j z)) ∧ (∀ k<n,∀ z∈Icc (-swing V n) (swing V n), HasDerivAt (g i k) (g i (k+1) z) z) ∧ ∀ z∈Icc (-swing V n) (swing V n),‖g i n z‖ ≤ Real.exp (T.scale i*b)
lemma Guard.alive (h:Guard T x s a f b)(he:T.Costs s (-a))(hp:∀ i,0<s i) (hf:∀ y:I→ V→ E4,Neighbors T x y a→ (∀ j:V × Axis,∀ᶠ i in T.via, period (y i) (s i) j)→T.Costs (fun i=> f i (y i)) b) : T.Costs (fun i=> f i (x i)) b:=by
   let free (K:Finset (V×Axis)):= ∀ y, Neighbors T x y a→ (∀ j:V × Axis,j∉K→∀ᶠ i in T.via,period (y i) (s i) j) → T.Costs (fun i=> f i (y i)) b
   have hy(K:Finset (V×Axis)): free K:=by
       induction K using Finset.induction_on with
       | empty=> exact fun y hx h=> hf y hx (fun i=>h i (Finset.notMem_empty i))
       | @insert j K hi ih=>
          intro y hx hv; obtain ⟨n,g,hG⟩:=h y hx j; let p:= swing V n
          choose w hw hW using fun i:I=> strideArced (y i) (s i) j n (hp i)
          let y' (k:Fin (2^n))(i:I):= wag (y i) (s i) j (w i k)
          have hn(k):T.Costs (fun i=>f i (y' k i)) b:= by
             refine ih (y' k) (hx.trans (wag_neighbors j he (Costs.unlimited p (Eventually.of_forall fun i=>abs_le.mpr ((hw i).1 k))))) ?_; intro i he; by_cases h:i=j; subst i; exact Eventually.of_forall fun i=>hW i k;
             exact (hv i (fun h'=>(Finset.mem_insert.mp h').elim h he)).mono fun i hp=> wag_preserves _ _ _ _ h _ hp -- name clash
          have hs(k:Fin (2^n)):= (hn k).cf (g:=fun i:I=> g i 0 (w i k)) (hG.mono (fun i hi=> (congr_fun hi.1 (w i k)).symm))
          refine (Fareway.Costs.stencilW (swing_pos n) hw hs (hG.mono (fun i hi=> hi.2.1)) (fun t=> Costs.allows_norm (T.minted b|>.pay) (hG.mono (fun i hi=>hi.2.2 (t i) (t i).property)))).cf ?_; filter_upwards [hG] with i hi; simp only [hi.1,wag_zero]
   exact hy Finset.univ x Neighbors.rfl (fun i h=>(h (mem_univ i)).elim)
end YM.Frontier6.Road
