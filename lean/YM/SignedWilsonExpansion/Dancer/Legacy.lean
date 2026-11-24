import YM.SignedWilsonExpansion.F9.Hem
import YM.XSpace.LimitWork
/-! Auxiliary analysis solely on finite-dimensional spaces; account `o` independent slots.Price -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace Normalize Future Gauge Labels Filter Function Matrix
open scoped BigOperators Topology Classical
variable {G:Gauge}{d h n s:ℕ}{ι σ E F K M:Type*}{l:Filter ι} {Q U:ℝ}
-- By K-weak convergence
namespace SeatsW
variable [NontriviallyNormedField K] [AddCommGroup E][Module K E][AddCommGroup F][Module K F]
variable {p q:ι→E}{x y:E}
lemma translate (L:E→ₗ[K] F)(h:By K l p x) : By K l (L ∘ p) (L x):=translateBy L h
lemma addY (h:By K l p x)(t:By K l q y): By K l (fun i=> p i+q i) (x+y) := fun a=>by simp_rw [map_add]; exact (h a).add (t a)
lemma subY (h:By K l p x)(t:By K l q y): By K l (fun i=> p i-q i) (x-y) := fun a=>by simp_rw [map_sub]; exact (h a).sub (t a)
lemma scaleY {c:K}{y:ι→K} (v:Tendsto y l (𝓝 c)) (h:By K l p x): By K l (fun i=> y i • p i) (c • x):=fun a=> by simp_rw [map_smul]; exact v.mul (h a)
lemma monoY {l': Filter ι}(h:By K l p x)(v:l'≤l): By K l' p x:= fun a=> (h a).mono_left v
lemma viaY (h:By K l p x)(v:p=ᶠ[l]q): By K l q x:= fun a=>(h a).congr' (v.fun_comp a)
lemma sumY (P : σ→ι→E) {t:σ→ E}(s:Finset σ)(h:∀ i∈s,By K l (P i) (t i)): By K l (fun i=>∑ j∈s,P j i) (∑ i∈s,t i):=fun a=>by simp_rw [map_sum]; exact tendsto_finsetSum s fun i hi=>h i hi a
lemma constant (t:E): By K l (fun _=> t) t:=fun _=>tendsto_const_nhds
lemma zin (l:Filter ι)(P:ι→ ℝ)(h:Tendsto P l (𝓝 0)) : By ℝ l P 0 := fun x=> x.continuous_of_finiteDimensional.continuousAt.tendsto.comp h
section finite
variable [FiniteDimensional K E]
abbrev Stock (B:Module.Basis σ K E)[Fintype σ](h:By K l p x) : Tendsto (fun i=> B.equivFun (p i)) l (𝓝 (B.equivFun x)) := tendsto_pi_nhds.mpr fun j=> h (B.coord j) -- abbrev Prop/test
lemma uptake (B:Module.Basis σ K E)[Fintype σ](h: Tendsto (fun i=> B.equivFun (p i)) l (𝓝 (B.equivFun x))) : By K l p x:= redeemBy B.coord (fun x u=> B.equivFun.injective (by rw [map_zero]; funext i; exact u i)) (fun i:σ=>tendsto_pi_nhds.mp h i)
lemma solitary [l.NeBot] (h:By K l p x)(v:By K l p y): x=y:= (Module.finBasis K E).equivFun.injective (tendsto_nhds_unique (Stock (Module.finBasis K E) h) (Stock _ v))
theorem regroup [Module ℂ E] (U:Ultrafilter ι) (B:Module.Basis σ ℂ E)[Fintype σ] (q:ι→E) (t:ℝ) (h:∀ᶠ i in (U:Filter _), ‖B.equivFun (q i)‖≤ t) : ∃ x:E,By ℂ (U:Filter _) q x := by
   let e(i):= B.equivFun (q i); obtain ⟨y,-,hy⟩:= (isCompact_closedBall (0:σ→ℂ) t).ultrafilter_le_nhds (U.map e) (Filter.le_principal_iff.mpr (h.mono fun i hi=> Metric.mem_closedBall.mpr ( (dist_zero_right (e i)).trans_le hi))); letI:FiniteDimensional ℂ E:= Module.Finite.of_basis B; exact ⟨B.equivFun.symm y,uptake B (by rw [LinearEquiv.apply_symm_apply]; exact hy)⟩
lemma regularX (hc : ∀ U:Ultrafilter ι,(U:Filter _)≤l→ By K (U:Filter _) p x): By K l p x:=fun a=>tendsto_iff_comap.mpr (Filter.le_iff_ultrafilter.mpr (fun U hu=>tendsto_iff_comap.mp (hc U hu a)))
lemma throttle (v:ι→ℝ) (h:∀ U:Ultrafilter ι,(U:Filter _)≤l→¬ Tendsto v (U:Filter _) atTop): ∃ t:ℝ,∀ᶠ i in l,v i≤t:=by
   by_contra! w
   let L:=l ⊓ Filter.comap v atTop
   have HE:L.NeBot:= inf_neBot_iff_frequently_right.mpr fun {T} P => by
      obtain ⟨s,hs,H⟩:= Filter.mem_comap.mp P
      obtain ⟨y,hy⟩:= mem_atTop_sets.mp hs
      exact (w y).mono fun i h=> H (hy _ h.le)
   obtain ⟨U,hu,hv⟩:= (exists_ultrafilter_iff.mpr HE).imp (fun U H=> le_inf_iff.mp H)
   exact h U hu (tendsto_iff_comap.mpr hv)
lemma collectReal [Module ℂ E] [FiniteDimensional ℂ E] [Module ℝ E][IsScalarTower ℝ ℂ E](h:By ℝ l p x): By ℂ l p x:=by
   intro a; have hf:= h (Complex.reCLM.toLinearMap.comp (a.restrictScalars ℝ)); have hz:= h (Complex.imCLM.toLinearMap.comp (a.restrictScalars ℝ)); have he:Tendsto (fun i=>(((a (p i)).re:ℝ):ℂ)) l (𝓝 ((↑(a x).re):ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp hf; have hi:Tendsto (fun i=>(((a (p i)).im:ℝ):ℂ)) l (𝓝 ((↑(a x).im):ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp hz; simpa only [Complex.re_add_im] using he.add (hi.mul_const Complex.I)
lemma payReal [Module ℂ E] [Module ℝ E][IsScalarTower ℝ ℂ E][FiniteDimensional ℂ E] (h:By ℂ l p x): By ℝ l p x:=by
   -- expand finite complex basis & R-linear all
   let B:=Module.finBasis ℂ E; intro a; let f(v:E)(j):= (B.equivFun v) j; have he(x:E): a x=∑ i, a ((f x i) • B i):=by nth_rw 1 [← B.sum_repr x]; rw [map_sum]; rfl
   let A(i): ℂ→ₗ[ℝ]ℝ:= a.comp ( (LinearMap.smulRight (LinearMap.id : ℂ→ₗ[ℂ]ℂ) (B i)).restrictScalars ℝ ); rw [he x]; rw [funext (fun i:ι=> he (p i))]; exact tendsto_finsetSum _ fun i _=> ( ( A i ).continuous_of_finiteDimensional.tendsto _ ).comp (h (B.coord i))
variable {A:ι→ E→ₗ[K] F}{T:E→ₗ[K] F}
lemma fixed [Fintype σ](B:Module.Basis σ K E)(h:∀ j, By K l (fun i=> A i (B j)) (T (B j))) (p:E) : By K l (fun i=> A i p) (T p):=by
    rw [← B.sum_repr p]; simp_rw [map_sum,map_smul]; exact sumY _ _ (fun i _=> scaleY tendsto_const_nhds (h i))
lemma flowing (h:∀ t, By K l (fun i=> A i t) (T t))(v:By K l p x): By K l (fun i=> A i (p i)) (T x) := by
    let B:=Module.finBasis K E; rw [← B.sum_repr x,map_sum]; simp_rw [map_smul]; refine viaY (sumY (fun j i=> B.coord j (p i) • A i (B j)) _ (fun i _=> scaleY (v (B.coord i)) (h (B i)))) (Eventually.of_forall fun i=> ?_); dsimp only; nth_rw 2 [← B.sum_repr (p i)]; rw [map_sum]; exact Finset.sum_congr rfl fun j _=> (map_smul (A i) _ _).symm
lemma byShips (h:∀ t, By K l (fun i=>A i t) (T t))[FiniteDimensional K F] : By K l A T:=by
    let B:=Module.finBasis K E; let V:=Module.finBasis K F; refine redeemBy (fun i:Fin (Module.finrank K E) × Fin (Module.finrank K F) => ( V.coord i.2 ).comp ( LinearMap.applyₗ (B i.1) ) ) (fun M h=> B.ext (fun i => ?_)) (fun i=> h (B i.1) (V.coord i.2)); rw [LinearMap.zero_apply (x:=B i)]; apply V.equivFun.injective; rw [map_zero]; funext j; exact h (i,j)
end finite
section costO
open Asymptotics
-- avoid conflicting imported O_ definition notation.
variable {s:ι→ℝ}
abbrev Discount (K:Type*) [NontriviallyNormedField K][Module K E](l:Filter ι) (s:ι→ℝ)(p:ι→E) := ∀ T:Module.Dual K E, (fun i=> T (p i))=o[l] s
-- Lean warnings duplicate `[AddCommGroup E]` harmless?
abbrev Salary (K:Type*) [NontriviallyNormedField K][Module K E](l:Filter ι) (s:ι→ℝ)(p:ι→E) := ∀ T:Module.Dual K E, (fun i=> T (p i))=O[l] s
lemma income (h:By K l p x): Salary K l 1 p:= fun T=> isBigO_const_of_tendsto (h T) one_ne_zero
lemma sunrise (h:Discount K l s p)(v:s=O[l] (1:ι→ℝ)) : By K l p 0:=by intro T; rw [map_zero]; exact (isLittleO_one_iff ℝ).mp ((h T).trans_isBigO v)
lemma cheapens (h:Discount K l s p)(T:E→ₗ[K] F): Discount K l s (T ∘ p):=fun a=> h (a ∘ₗ T)
lemma translates (h:Salary K l s p)(T:E→ₗ[K] F): Salary K l s (T ∘ p):=fun a=> h (a ∘ₗ T)
end costO
end SeatsW
end YM.SignedWilsonExpansion.Dancer
