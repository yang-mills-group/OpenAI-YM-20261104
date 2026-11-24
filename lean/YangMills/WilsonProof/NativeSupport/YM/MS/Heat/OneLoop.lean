import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Racey
/-!
# One-loop: no leftover term

Transport assumptions use primitive integrals, not scheme equality or even UV gains.
 Kim kernels can be measured on topological cover or continuum. $μ$ integrates
 compact smooth (sharp) for proof. Need extension to analytic-$d$ separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open scoped Topology ContDiff
-- Measure μ. Cycle Ost ordinarily requires add-only or Cost asks Borel finiteDim
variable {P I A:Type} [MeasurableSpace P] [AddCommGroup P][Fintype A]{p: Sector A}{K L: Flux A P ℂ} {F H:Row A P ℂ}(μ:Measure P){q:P}

abbrev Ccy (K:Flux A P ℂ)(F:Row A P ℂ)(μ:Measure P): Row A P ℂ:= fun w=> ∫ q,trc K q F w ∂μ
def Pass (K:Flux A P ℂ)(F:Row A P ℂ)(μ:Measure P): Prop:= ∀ l, Integrable (fun q=>trc K q F l) μ
lemma cycle_map {J:Type}(P:(Row A P ℂ)→ J→ℂ)(hx:Sensible P) w (hf:Pass K F μ): Integrable (fun q=> P (trc K q F) w) μ ∧ P (Ccy K F μ) w= ∫ q,P (trc K q F) w ∂μ:= by
   have he:= cent_arguments μ (hx.reaches w) hf; exact ⟨he.1,he.2.symm⟩

lemma scatter_integral {A I:Type}[MeasurableSpace I](μ:Measure I){f:I→ Shared A ℂ} (p:Sector A)(l:Legs A)(hp:∀ a b, Split a b l → Integrable (fun q=> f q a b) μ) : Integrable (fun q=> scatter p l (f q)) μ ∧ (∫ q,scatter p l (f q) ∂μ)=scatter p l (fun a b=>∫ q,f q a b ∂μ):= by
   -- by cent_arguments on Pair list if able integrate all w, but this version
   induction l generalizing f with
   | nil=> exact ⟨hp _ _ .nil,rfl⟩
   | cons i l ih=>
      let g (q:I)(a b:Legs A):= f q (i::a) b+cross (p i) (degree p a)* f q a (i::b); have hx : ∀ a b,Split a b l→ Integrable (fun q=>g q a b) μ:= fun a b h=> (hp _ _ h.left).add ((hp _ _ h.right).const_mul _); obtain ⟨hr,hs⟩:= ih (f:=g) hx; refine ⟨hr,?_⟩; rw [show (∫ q, scatter p (i::l) (f q) ∂μ)= _ from hs,scatter_cons]; apply scatter_congr; intro a b he; unfold g; rw [integral_add (hp _ _ he.left) ((hp _ _ he.right).const_mul _), integral_const_mul]
-- ASSUMPTIONS frame routes
structure Route (K L:Flux A P ℂ)(p:Sector A)(F H:Row A P ℂ)(μ:Measure P): Prop where
    lf (l r a e i j): Integrable (hits p K L F H l r a e i j) μ
    rf (l r a e i j): Integrable (restL p K L F H l r a e i j) μ
    flip (l r a e i j): (∫ u, restL p K L F H l r a e i j (-u) ∂μ)=∫ u,restL p K L F H l r a e i j u ∂μ
    -- only this root vector shift on real μ? D analytic needs stronger form.
    shift (l r a e i j): (∫ u,hits p K L F H l r a e i j (- net l-u) ∂μ)=∫ u,hits p K L F H l r a e i j u ∂μ

-- sum-4 convenience
omit [AddCommGroup P] in
lemma pays4 (f:A→A→A→A→P→ℂ)(h:∀ i j k l, Integrable (f i j k l) μ): Integrable (fun q=>∑ a,∑ i,∑ k,∑ l,f a i k l q) μ ∧ (∫ q, ∑ a,∑ i,∑ k,∑ l,f a i k l q ∂μ)=∑ a,∑ i,∑ k,∑ l,∫ q,f a i k l q ∂μ:= by
    have he a i k: Integrable (fun q=>∑ l,f a i k l q) μ:= integrable_finsetSum _ (fun l _=> h ..); have hv a i: Integrable (fun q=>∑ k,∑ l,f a i k l q) μ:= integrable_finsetSum _ (fun l _=> he ..); have hm a: Integrable (fun q=>∑ i,∑ k,∑ l,f a i k l q) μ:= integrable_finsetSum _ (fun i _=> hv ..)
    exact ⟨integrable_finsetSum _ (fun i _=> hm i), by rw [integral_finsetSum _ (fun i _=> hm i)]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [integral_finsetSum _ (fun i _=> hv a i)]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [integral_finsetSum _ (fun k _=> he a i k)]; refine Finset.sum_congr rfl fun k _=> integral_finsetSum _ (fun l _=>h ..)⟩
-- one-loop result
lemma hits_base (h: Route K L p F H μ) (hr:Reverse L p)(l:Legs (Mode A P)): Integrable (pairedX p K L F H l) μ ∧ (∫ q,pairedX p K L F H l q ∂μ)=scatter (field p) l (fun a b=> 2*∑ i,∑ j,∑ k,∑ t,∫ q,hits p K L F H a b i j k t q ∂μ):= by
    let f (a b: Legs (Mode A P)) i j k t := hits p K L F H a b i j k t + restL p K L F H a b i j k t
    let V (q:P)(a b:Legs (Mode A P)):= ∑ i,∑ j,∑ k,∑ t,f a b i j k t q
    have he a b := pays4 μ (f a b) (fun i j k t=> (h.lf a b i j k t).add (h.rf ..)); obtain ⟨hL,hM⟩:= scatter_integral μ (f:=V) (field p) l (fun a b _=> (he a b).1); refine ⟨hL,hM.trans ?_⟩; apply scatter_congr; intro a b hab;
    let U:= hits p K L F H a b; rw [(he a b).2]; -- may V need unfold
    have ht i j k l : (∫ q, f a b i j k l q ∂μ)=(∫ q, U i j k l q ∂μ)+(∫ q, U j i k l q ∂μ) := by
        unfold f; simp only [Pi.add_apply]; rw [integral_add (h.lf ..) (h.rf ..),← h.flip]; simp_rw [RL hr] -- abbreviation
        rfl
    simp_rw [ht,Finset.sum_add_distrib]; rw [two_mul]; congr 1; rw [Finset.sum_comm]
variable {b c:Bool}
lemma switch (he:b=false ∨ c=false)(hk:closed K p b)(hL:closed L p c)(X:Route K L p F H μ)(Y:Route L K p F H μ)(hv: Reverse L p)(hr: Reverse K p)(hf: Symm (field p) F)(hg:Symm (field p) H) (w: Legs (Mode A P)): (∫ u, pairedX p K L F H w u ∂μ)=∫ u,pairedX p L K F H w u ∂μ:= by
   rw [(hits_base μ X hv w).2,(hits_base μ Y hr w).2]; apply scatter_congr; intro a t _; simp_rw [dance_X he hk hL _ _ _ _ _ hf hg,Y.shift]; rw [summ_sum]; -- adjust direction
lemma cross_cycle (hP: Pass L F μ)(hh:Pass L H μ)(h1: Route K L p F H μ)(ht:Reverse L p)(hj:Reverse K p)(hF:Symm (field p) F)(hH:Symm (field p) H)(hp:Pure (field p) false F) (hk:closed K p b) (hl:closed L p c)(hv:b=false ∨ c=false)(w: Legs (Mode A P)):
    Ccy L (tree p K F H) μ w= tree p K (Ccy L F μ) H w + tree p K F (Ccy L H μ) w + ∫ u, pairedX p K L F H w u ∂μ:= by
   have ht' := hits_base μ h1 ht w
   obtain ⟨hA,hB⟩:= cycle_map μ (fun z=>tree p K z H) (sense_atLeft ..) w hP; obtain ⟨hU,hV⟩:= cycle_map μ (tree p K F) (sense_atRight ..) w hh -- edit
   unfold Ccy; simp_rw [tierX hv hk hl hj w _ hF hH hp]; rw [integral_add _ ht'.1]; rw [integral_add hA hU,← hB,← hV]; exact hA.add hU -- may rfl
-- no extension calls.
lemma exchange_term (hP: Pass L F μ)(hh:Pass L H μ)(hq:Pass K F μ)(ht:Pass K H μ)(h1: Route K L p F H μ)(hr:Route L K p F H μ)(hv:Reverse L p)(hj:Reverse K p)(hF:Symm (field p) F)(hH:Symm (field p) H)(hp:Pure (field p) false F) (hk:closed K p false) (hl:closed L p true):
    Ccy L (tree p K F H) μ + tree p L (Ccy K F μ) H+ tree p L F (Ccy K H μ)= Ccy K (tree p L F H) μ + tree p K (Ccy L F μ) H+ tree p K F (Ccy L H μ) := by
    ext w; simp only [Pi.add_apply]; rw [cross_cycle μ hP hh h1 hv hj hF hH hp hk hl (Or.inl rfl), cross_cycle μ hq ht hr hj hv hF hH hp hl hk (Or.inr rfl), switch μ (Or.inl rfl) hk hl h1 hr hv hj hF hH]; abel
end YM.MS.Heat
