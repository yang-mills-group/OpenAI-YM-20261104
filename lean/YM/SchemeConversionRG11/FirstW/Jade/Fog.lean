import YM.SchemeConversionRG11.FirstW.Jade.Vital
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped Topology BigOperators Classical
variable {T:Itinerary}{G:Gauge}{o:StepPath T}{K:Set E4}{A B:Sight T G}
lemma costs_rush (h:HatP T K A)(hk:(0:E4)∈K)(k:ℕ)(hv:k≤2): Helen (fun i=> (T.gap i^k)⁻¹ • rush G 0 k (A i) (A i)):= by
 let f (i:ℕ):= (T.gap i ^ k)⁻¹ • rush G 0 k (A i) (A i)
 have hh(i j:Axis)(γ: Fin k→ Axis): Helen (fun m=> f m i j γ) := by
   unfold f; simp only [rush,Pi.smul_apply,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.sum_apply,patched_q,smul_add,Finset.sum_add_distrib] -- simp_rw of ← smul_sum maybe factors conv
   let X:Hall T G.Color:= fun l x=> swerve x (square i j) (A l) (A l)
   obtain ⟨S,H⟩:= (wellP h h (square i j)); obtain ⟨Y,e⟩:= pleased_lim (show Pleased T K (surface (List.ofFn γ) X) from ⟨_,H.insect (List.ofFn γ)⟩) hk
   simp_rw [shifts_add] at e
   obtain ⟨P,F⟩:= brief_j h hk k hv i j γ; let L:ℝ:= (k.factorial:ℝ)⁻¹
   have ht:= (e.const_smul L).add (F.const_smul (2:ℝ)|>.const_smul L); refine ⟨_,ht.congr fun m=>?_⟩; simp only [X,L]; simp only [Finset.smul_sum,smul_smul]; ring_nf
 choose y hy using hh
 exact ⟨y, tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mpr (fun γ=> hy i j γ)))⟩
def nativeM (T:Itinerary)(A:Sight T G)(i:ℕ):FullT G (T.period i):= T.gap i • A i
lemma praise_echo (h:HatP T K A)(hk:(0:E4)∈K)(a:Labels.Key G)(ha:a.fst ≤2): Helen (fun i=> echoLeg (T.gap i) 0 a (nativeM T A i) (nativeM T A i)):= by
 let k:=a.fst; let V (s:Signed)(i:ℕ):= rush G 0 k (actC T s A i) (actC T s A i)
 let L (s:Signed): Bare.Response G k →ₗ[ℝ] ℝ := (Labels.axes G k).coord a.2 ∘ₗ Labels.Taylor.turn s.ortho ∘ₗ Bare.radialMap
 let f (s:Signed)(i:ℕ):= L s ((T.gap i ^ k)⁻¹ • V s i)
 have H(s:Signed): Helen (f s):=by
    have hz:= (show (0:E4)∈ (Ortho.move s.ortho) ⁻¹' K from by simp only [mem_preimage]; rw [show Ortho.move s.ortho 0=0 from (Ortho.motion s.ortho).map_zero]; exact hk)
    obtain ⟨x,h⟩:= costs_rush (heat_hats h s) hz k ha
    exact ⟨L s x,(L s).continuous_of_finiteDimensional.continuousAt.tendsto.comp h⟩
 let P:ℝ := 1/2 * (Fintype.card Signed:ℝ)⁻¹
 obtain ⟨y,Y⟩:= collectH Finset.univ f (fun i _=> H i)
 refine ⟨P*y, (Y.const_mul P).congr fun i =>?_⟩
 have ht : ((T.gap i ^(mass a))⁻¹)= (T.gap i ^ k)⁻¹*(T.gap i ^2)⁻¹ := by rw [mass,pow_add, mul_inv] -- check
 simp only [echoLeg,echoAt,nativeM,map_smul,LinearMap.smul_apply,LinearMap.compr₂_apply, glint_once,sheer_eq,affine,Signed.act_zero,zero_add,map_add,map_sum,f,V,actC,L,LinearMap.comp_apply,ht,smul_eq_mul,← Finset.mul_sum]; unfold P k; apply (show ∀ u t w:ℝ,1/2*u*(w*t)=T.gap i*(T.gap i*(w*(T.gap i ^2)⁻¹*(1/4*(u*t+u*t)))) from fun u t w=>by field_simp [(T.positive i).ne']; ring)
lemma praises (h:HatP T K A)(hp:HatP T K B)(hk:(0:E4)∈K)(a:Labels.Key G)(ha:a.fst ≤2): Helen (fun i=> echoLeg (T.gap i) 0 a (nativeM T A i) (nativeM T B i)):=by
 let C:= A+B; have hc: HatP T K C:= fun j=> (h j).enclose (hp j)
 obtain ⟨x,H⟩:=praise_echo h hk a ha; obtain ⟨y,Y⟩:= praise_echo hp hk a ha; obtain ⟨z,HZ⟩:= praise_echo hc hk a ha
 refine ⟨_,(((HZ.sub H).sub Y).div_const 2).congr fun i=>?_⟩
 have he {E:Type}[AddCommGroup E][Module ℝ E](L:E→ₗ[ℝ] E→ₗ[ℝ]ℝ)(x y:E)(hv:L y x=L x y): (L (x+y) (x+y)-L x x-L y y)/2=L x y := by simp only [map_add,LinearMap.add_apply,hv]; ring
 rw [show nativeM T C i=nativeM T A i+nativeM T B i from by simp only [nativeM,C,Pi.add_apply,smul_add]]; apply he; simp only [echoLeg,LinearMap.smul_apply]; rw [echoAt_symm]
end YM.RG11.FirstW
