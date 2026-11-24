import YM.SchemeConversionRG11.FirstW.Trice.Face
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {n:Side}{T:Itinerary}{G:Gauge}{W:Axis→ Axis→G.Color}{f:Sight T G}
lemma curlL_s (f:FullT G n) (s:Signed) (i j:Axis)(x:Cover): Bare.wideCurl (Bare.wideLink G s f) (wrap n x) i j=(violet s i*violet s j) • Bare.wideCurl f (wrap n (s.act x+(bottomK s i+bottomK s j))) (s.perm i) (s.perm j):= by
 have hp:= congrFun (slide_curl (terms (0:Site n) f) s i j) x
 simp only [terms_pull,Signed.act_zero,curlK,Pi.smul_apply,←frontRail,rail_wrap,add_zero] at hp; simpa only [←frontRail] using hp
lemma recore (v:FullT G n) (i j:Axis)(x:Site n)(s:Fin 0→Axis): Bare.wideCore G 0 x v i j s=Bare.wideCurl v x i j:= by
 rw [Bare.wideCore_apply,Finset.sum_eq_single_of_mem (∅:Finset (Fin 0)) (Finset.mem_univ _) (fun p _ e=> False.elim (e (Subsingleton.elim ..)))]; simp [Bare.sign]
def consoleS (n:Side)(t:ℝ): FullT G n →ₗ[ℝ] Labels.Taylor G 0:= t • Bare.wideLinear G 0 1 (0:Site n)
lemma vote (h:∀ i j,W i j= -W j i)(hf:∀ i j:Axis,∀ x:Cover,Tendsto (fun k=> (T.gap k)⁻¹ • Bare.wideCurl (f k) (wrap (T.period k) x) i j) atTop (𝓝 (W i j))) : Tendsto (fun i=> consoleS (T.period i) (T.gap i)⁻¹ (f i)) atTop (𝓝 (Bare.radialMap (door W))) := by
 let Y(s:Signed):= door (fun i j=> (violet s i*violet s j) • W (s.perm i) (s.perm j)); let p(s:Signed)(i:ℕ):=Bare.wideCore G 0 (0:Site (T.period i)) (Bare.wideLink G s (f i)); let L(s:Signed):= Labels.Taylor.turn s.ortho (j:=0) (G:=G) ∘ₗ Bare.radialMap
 have hX(s:Signed): Tendsto (fun k=>L s ((T.gap k)⁻¹ • p s k)) atTop (𝓝 (Bare.radialMap (door W))):= by
   rw [←radial_view W h s]; change Tendsto _ _ (𝓝 (L s (Y s))); apply (L s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (show Tendsto (fun k=> (T.gap k)⁻¹ • p s k) atTop (𝓝 (Y s)) from ?_)
   refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mpr fun γ=>?_)); simp only [p,Y,Pi.smul_apply,recore,door]
   apply ((hf _ _ (bottomK s i+bottomK s j)).const_smul _).congr; intro k; rw [smul_comm]; apply congrArg _; exact (by simpa only [map_zero, Signed.act_zero,zero_add] using (curlL_s (f k) s i j 0).symm)
 let c:ℝ:= (Fintype.card Signed:ℝ)⁻¹; have he:= tendsto_finsetSum Finset.univ (fun i _=> hX i) |>.const_smul c
 rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,show ∀ v:Labels.Taylor G 0,c • ((Fintype.card Signed:ℝ) • v)=v from fun v=>inv_smul_smul₀ (by exact_mod_cast Fintype.card_ne_zero) _] at he
 apply he.congr; intro i; simp only [L,c,p,map_smul, LinearMap.comp_apply,← Finset.smul_sum]; simp only [consoleS,Bare.wideLinear,LinearMap.smul_apply,LinearMap.sum_apply, LinearMap.comp_apply,one_zpow,one_smul,affine,Signed.act_zero,add_zero]; rw [smul_comm]
lemma ray_life (W:Axis→Axis→ G.Color) (hf:∀ i j:Axis,∀ x:Cover,Tendsto (fun k=> ray i (stalkH T f j) k (wrap (T.period k) x)) atTop (𝓝 (W i j))) : Tendsto (fun i=> consoleS (T.period i) (T.gap i)⁻¹ (f i)) atTop (𝓝 (Bare.radialMap (door (fun i j=> W i j-W j i)))) := by
 apply vote (fun i j=>by rw [neg_sub]); intro i j x
 apply ((hf i j x).sub (hf j i x)).congr; intro k; let p:= wrap (T.period k) x; change ray i (stalkH T f j) k p-ray j (stalkH T f i) k p=_ • Bare.wideCurl (f k) p i j
 simp only [ray,surface,List.length_singleton,pow_one,Pi.smul_apply,combine,up,stalkH,Bare.wideCurl,←smul_sub]; apply congrArg _; abel
end YM.RG11.FirstW
