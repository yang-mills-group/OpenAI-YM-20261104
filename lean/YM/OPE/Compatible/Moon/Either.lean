import YM.OPE.Compatible.Moon.Gravity
/-! # stability of limits of cross-epoch orientations. No lower period assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Luke
open Next.Rank Next.Rank.Price Owl
open scoped Topology Classical BigOperators
variable {d k N i:ℕ} {G:Gauge}{C:Family G}(T:C.Makes)
variable {I E F Q:Type} {r L t v C:ℝ}{φ: Filter I} [φ.NeBot]
variable {J: Fin (d+1)→Type}[∀ i,NormedAddCommGroup (J i)][∀ i,NormedSpace ℂ (J i)][∀ i,FiniteDimensional ℂ (J i)]
variable {p:I→ Train J} {f:Train J}
omit [φ.NeBot] [∀ i,FiniteDimensional ℂ (J i)] in lemma zoot (h:Tendsto p φ (𝓝 f))(i j:Fin (d+1)): Tendsto (fun k=> route (p k) i j) φ (𝓝 (route f i j)):= pulp (tendsto_const_nhds (x:=ContinuousLinearMap.single ℂ J j)) (pulp h (tendsto_const_nhds (x:=ContinuousLinearMap.proj i)))
omit [∀ i,FiniteDimensional ℂ (J i)] in lemma rallyS (h:Tendsto p φ (𝓝 f))(he:∀ᶠ i in φ,team (p i)):team f:= fun i j hi=> tendsto_nhds_unique_of_eventuallyEq (zoot h i j) tendsto_const_nhds (he.mono fun _ h=>h i j hi)
local notation "V"=> Dock J
variable {U:I→ Dock J≃L[ℂ] Dock J}
variable (h:Tendsto (fun i=>(U i).toContinuousLinearMap) φ (𝓝 f))
variable (he:∀ᶠ i in φ, Treaty L t C (U i))
include he h
omit [∀ i,FiniteDimensional ℂ (J i)] in
lemma compass {a:Train J}(hz:Tendsto (fun i=>(U i).symm.toContinuousLinearMap) φ (𝓝 a)) :∃ P: V≃L[ℂ]V, f=P.toContinuousLinearMap∧ Treaty L t C P:=by
        have hp:f.comp a=ContinuousLinearMap.id ..:=tendsto_nhds_unique_of_eventuallyEq (pulp hz h) (tendsto_const_nhds) (Eventually.of_forall fun i=> ContinuousLinearMap.ext (fun x=> (U i).apply_symm_apply x))
        have hh:a.comp f=ContinuousLinearMap.id ..:=tendsto_nhds_unique_of_eventuallyEq (pulp h hz) (tendsto_const_nhds) (Eventually.of_forall fun i=> ContinuousLinearMap.ext (fun x=>(U i).symm_apply_apply x))
        let P: V≃L[ℂ] V:= { f.toLinearMap with
                toFun:=f
                invFun:=a
                left_inv:= fun j=>DFunLike.congr_fun hh j
                right_inv:=fun j=>DFunLike.congr_fun hp j
                continuous_toFun:= f.cont
                continuous_invFun:= a.cont }
        have hy:Tendsto (fun i=>(U i).symm.toContinuousLinearMap) φ (𝓝 P.symm.toContinuousLinearMap):=hz; exact ⟨P,rfl,rallyS h (he.mono fun _ hi=>hi.toC),rallyS hy (he.mono fun _ hi=>hi.ofC),fun i=>le_of_tendsto (zoot h i i).norm (he.mono fun _ hi=>hi.grace i),fun i=> le_of_tendsto (zoot hy i i).norm (he.mono fun _ hi=>hi.value i),le_of_tendsto h.norm (he.mono fun _ hi=>hi.charge),le_of_tendsto hy.norm (he.mono fun _ hi=>hi.inverse)⟩
omit h he [φ.NeBot]
section
variable {X: Type}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
variable (A: Ultrafilter I) {P Q:I→ X →L[ℂ] Dock J}{W:I→ X→L[ℂ] X}{W': X→L[ℂ] X}{p q:X→L[ℂ] Dock J}
omit [FiniteDimensional ℂ X] in
lemma arriveS (hp:Tendsto P A (𝓝 p))(hq:Tendsto Q A (𝓝 q))(hw:Tendsto W A (𝓝 W'))(hE:∀ᶠ i in A,∃ T:Dock J≃L[ℂ] Dock J,Treaty L t C T ∧ ‖(P i).comp (W i) - T.toContinuousLinearMap.comp (Q i)‖≤v) : ∃ X': Dock J ≃L[ℂ] Dock J,Treaty L t C X' ∧‖p.comp W' - X'.toContinuousLinearMap.comp q‖≤v:=by
       letI:Nonempty (Dock J≃L[ℂ] Dock J):=⟨ContinuousLinearEquiv.refl ..⟩; obtain ⟨Q',hΨ⟩:= Eventually.choice hE; -- name
       have hT:= hΨ.mono (fun i hi=>hi.1); letI:=FiniteDimensional.proper ℂ (Train J); obtain ⟨X,hX⟩:=chant A (hT.mono fun i hi=> hi.charge); obtain ⟨Y,hY⟩:= chant A (hT.mono fun i hi=> hi.inverse); obtain ⟨K,H,hK⟩:= compass hX hT hY; subst X; exact ⟨K,hK,le_of_tendsto ((pulp hw hp|>.sub (pulp hq hX)).norm) (hΨ.mono fun i hi=> hi.2)⟩
lemma permitS (hp:Tendsto P A (𝓝 p))(hΨ:∀ᶠ i in A, ∃ b:Dock J→L[ℂ] X, (P i).comp b=ContinuousLinearMap.id .. ∧ ‖b‖≤v):∃ b:Dock J→L[ℂ] X, p.comp b=ContinuousLinearMap.id .. ∧ ‖b‖ ≤v:=by
       obtain ⟨f,hV⟩:= Eventually.choice hΨ; have hp':=hV.mono fun i hi=>hi.2; letI:=FiniteDimensional.proper ℂ (Dock J→L[ℂ] X); obtain ⟨a,ha⟩:= chant A hp'; exact ⟨a,tendsto_nhds_unique_of_eventuallyEq (pulp ha hp) tendsto_const_nhds (hV.mono fun i hi=> hi.1),le_of_tendsto ha.norm hp'⟩
end
end YM.OPE.Lake
