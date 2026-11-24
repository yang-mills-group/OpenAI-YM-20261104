import YM.SchemeConversionRG11.FirstW.Jade.Stems
import YM.SchemeConversionRG11.FirstW.Calx.Encore
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T:Itinerary} {A B: Type*} {G:Gauge} {V:Sight T G} {K:Set E4}{p q:E4}{n:Side}{k:ℕ}
def actC (T:Itinerary)(s:Signed)(v:Sight T G): Sight T G:=fun i=> Bare.wideLink G s (v i)
lemma sold (u:Signed)(w:StepPath T)(h:sails T w p): sails T (fun i=> u.act (w i)) (Ortho.move u.ortho p) := by
 let A i:=u.act (lift (w i)); have he: Tendsto (fun i=> Full.incVec (T.gap i) (A i)) atTop (𝓝 (Ortho.move u.ortho p)) := by
   change Tendsto (fun i=> Moss T i (u.act _)) _ _; simp_rw [moss_move]; exact (Ortho.motion u.ortho).continuous.continuousAt.tendsto.comp h
 have H:=sails_wrap he; convert! H using 1; funext i; simp only [A, ← wrap_signed,wrap_lift]
def circleR (T:Itinerary)(u:Signed)(f:Hall T G.Color): Hall T G.Color:=fun i x=> f i (u.act x)
lemma high_hats {f:Hall T G.Color}(u:Signed)(h:Pleased T K f): Pleased T ((Ortho.move u.ortho) ⁻¹' K) (circleR T u f) := by
 suffices H: ∀ D, ∃ Y, Meets T ((Ortho.move u.ortho) ⁻¹' K) (surface D (circleR T u f)) Y by choose y hy using H; exact ⟨y,hy⟩
 intro D; induction D generalizing f with
 | nil=> obtain ⟨Y,H⟩:=h; rw [surface_root]; exact ⟨fun v=>Y [] (Ortho.move u.ortho v), fun σ hs v hv p hp=> (show Tendsto _ _ _ from H.identity σ hs (Ortho.move u.ortho v) hv (fun i=>u.act (p i)) (sold (T:=Rig.path T σ hs) u p hp))⟩
 | cons i D ih=>
    let s:Step:= (posDir i).rotate u; let p:=circleR T u f; rw [surface_swap,←surface_surface]; change ∃ Y,Meets _ _ (surface D (ray i p)) Y
    have H: ray i p=circleR T u (slipC T f s):= funext fun i'=>funext fun x=>by
       simp only [s,ray,p,circleR,surface,Pi.smul_apply,combine,up, List.length_singleton,pow_one, slipC,Signed.act_add, Step.vec_rotate, Step.vec_pos]
    rw [H]; exact ih (h.slip s)
lemma heat_hats (h:HatP T K V)(u:Signed): HatP T ((Ortho.move u.ortho) ⁻¹' K) (actC T u V):= by
 intro i; let s:Step:= (posDir i).rotate u
 rw [show stalkH T (actC T u V) i=circleR T u (peakC T V s) from funext fun j=>funext fun x=>by simp only [actC,stalkH,Bare.wideLink_apply,circleR,peakC,boardAt, LinearMap.smul_apply, LinearMap.proj_apply]; unfold s; split <;> simp_all] -- name conditional h
 exact high_hats u (h.leg _)
-- sign sum on two slots for any ordering
lemma sign_two {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E](a:Fin 2→E): ∑ s:Finset (Fin 2), Bare.sign s • (∑ v∈s, a v)=0 := by
 rw [show Finset.univ (α:=Finset (Fin 2))={∅,{0},{1},{0,1}} by decide,Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]; norm_num [Bare.sign_eq, Finset.sum_insert]
lemma brief_j (h:HatP T K V) (hk:(0:E4)∈K)(k:ℕ)(hv:k≤2)(u v:Axis)(γ:Fin k→Axis):
 Helen (fun i=> (T.gap i ^ k)⁻¹ • ∑ s:Finset (Fin k), Bare.sign s • G.ad (rail 0 (Bare.walk γ s) (V i)) (rail (stop 0 (Bare.walk γ s)) (square u v) (V i))) := by
 -- B normalized open. rail square O(h). k=2 constant sum cancels. k=1 integrable. k=0 zero.
 let P:=rushC T V (posDir u) (posDir v); have hW: icon (posDir u) (posDir v)=square u v:= rfl
 have hp: Pleased T K P:= seesP h _ _
 have he(i:ℕ)(x:Site (T.period i)): rail x (square u v) (V i)= T.gap i • P i x:=by unfold P rushC; rw [hW,smul_inv_smul₀ (T.positive i).ne']
 obtain ⟨L,H⟩:= doubles G.ad
 interval_cases k
 · have e(s:Finset (Fin 0)) : Bare.walk γ s=[]:=by rw [Subsingleton.elim s ∅];simp [Bare.walk]
   simp_rw [e,rail,LinearMap.zero_apply,map_zero,LinearMap.zero_apply,smul_zero, Finset.sum_const_zero,smul_zero]; exact ⟨_,tendsto_const_nhds⟩ -- rail simplification could expand square
 · simp_rw [pow_one,Finset.smul_sum,he,map_smul]; apply collectH; intro s _; let W:= Bare.walk γ s; simp_rw [smul_comm ((T.gap _)⁻¹) (Bare.sign s), inv_smul_smul₀ (T.positive _).ne',←H]; exact pleased_lim (((walkP h W).map₂ (unwalking W hp) L).scale _) hk
 let Y(i:ℕ)(s:Finset (Fin 2)):= G.ad (cubeCost _ (Bare.walk γ s) (V i) 0) (P i 0)
 have hY(i:ℕ): ∑ s, Bare.sign s • Y i s=0:=by
    simp only [Y,walk_away]; let F:= G.ad.flip (P i 0); change ∑ s:Finset (Fin 2),Bare.sign s • F _=0; simp only [← map_smul, ←map_sum]; exact congrArg F (sign_two (fun j=>V i (0,γ j))) |>.trans (F.map_zero)
 let q (i:ℕ)(s:Finset (Fin 2)):= G.ad (rail 0 (Bare.walk γ s) (V i)) (P i (stop 0 (Bare.walk γ s)))
 have eY(i:ℕ): ∑ s:Finset (Fin 2),Bare.sign s • q i s= ∑ s:Finset (Fin 2),Bare.sign s • (q i s-Y i s):=by simp_rw [smul_sub,Finset.sum_sub_distrib,hY,sub_zero]
 simp_rw [he,map_smul,smul_comm (Bare.sign _) (T.gap _),←Finset.smul_sum]; change Helen (fun i=> (T.gap i ^2)⁻¹ • T.gap i • (∑ s,Bare.sign s • q i s)); simp_rw [eY,Finset.smul_sum]; apply collectH; intro s _
 let w:=Bare.walk γ s; let f(i:ℕ)(x: Site (T.period i)):= rail x w (V i); let Cs (i:ℕ)(x: Site (T.period i)):= cubeCost _ w (V i) x
 have e(i:ℕ): q i s-Y i s=L (f i 0) (P i (stop 0 w)-P i 0)+L (f i 0-Cs i 0) (P i 0):= by simp only [q,Y,f,Cs,w,H,map_sub,sub_apply]; abel
 have hz(i:ℕ) : (T.gap i ^ 2)⁻¹ * T.gap i=(T.gap i)⁻¹ := by field_simp
 simp_rw [smul_smul ((T.gap _ ^2)⁻¹) (T.gap _),hz,smul_comm _ (Bare.sign s),e,smul_add ((T.gap _)⁻¹)]; -- retain H works CLM.linear
 let B:Hall T G.Color:=fun i x=>(T.gap i)⁻¹ • (f i x-Cs i x)
 have h: Pleased T K (fun i x=> L (f i x) (straks T w P i x)+L (B i x) (P i x)):= ((walkP h w).map₂ (verst w hp) L).enclose ((slateE _ _ s h).map₂ hp L)
 obtain ⟨u,h⟩:= pleased_lim (h.scale (Bare.sign s)) hk; refine ⟨_,h.congr fun i=>?_⟩; simp [B,straks]
end YM.RG11.FirstW
