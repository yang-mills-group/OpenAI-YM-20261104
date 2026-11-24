import YM.XSpace.Singlet

/-!
# Tangent directions to the free color orbits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory Maxwell Maxwell.Free NormedSpace
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff
variable {G : Gauge}
section d
variable {E I F: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {Y:I→ E} {L:Filter I} {x v:E}
abbrev inspect (Y:I→E) (x:E) (i:I):= ‖Y i-x‖⁻¹ • (Y i-x)
lemma watches (hY:Tendsto Y L (𝓝 x)) (hy:Tendsto (inspect Y x) L (𝓝 v)) {f:E→F} {f':E→L[ℝ] F} (h:HasFDerivAt f f' x): Tendsto
    (fun i => ‖Y i-x‖⁻¹ • (f (Y i)-f x)) L (𝓝 (f' v)):=by
  let q (i:I):= ‖Y i-x‖⁻¹ • (f (Y i)-f x-f' (Y i-x)); have hh : Tendsto q L (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (((hasFDerivAt_iff_tendsto.mp h).comp hY).congr (fun i=> by simp [q,norm_smul]));
  have ht:= hh.add ((f'.continuous.tendsto v).comp hy); rw [zero_add] at ht; apply ht.congr; intro i; simp [q, inspect, smul_sub]
end d
variable {p : WickPol G} (F:Motor G)

def whip (t:ℝ):= exp (t • F)
lemma hit (t:ℝ) : HasDerivAt (whip F) (F*whip F t) t:= hasDerivAt_exp_smul_const' F t
@[simp] lemma whip0: whip F 0=1:=by rw [whip,zero_smul ℝ F, exp_zero]
lemma arc (h: OrthoDev F) (t:ℝ): Rot (whip F t):=by
  intro x; let f (t:ℝ):=whip F t x; let L:= ContinuousLinearMap.apply ℝ G.Color x; have he t : HasDerivAt f (F (f t)) t := L.hasFDerivAt.comp_hasDerivAt t (hit F t)
  have hh s : HasDerivAt (fun t=> ‖f t‖^2) 0 s :=by simpa [h (f s)] using (he s).norm_sq
  have ht:= is_const_of_deriv_eq_zero (fun s=>(hh s).differentiableAt) (fun s=>(hh s).deriv) t 0
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa [f] using ht)

lemma stiff (H : ∀ T,differ p T F=0) (T:TaylorTower G) (t:ℝ): play p T (whip F t)=probe T p:=by
  have he (t:ℝ): HasDerivAt (play p T ∘ whip F) 0 t:= by
    let R:=whip F t; let U:=motor R T; let f:Motor G→Motor G:=fun g=>g*R
    let L:Motor G→L[ℝ] Motor G:= LinearMap.toContinuousLinearMap
      { toFun := f
        map_add' x y:=add_mul x y R
        map_smul' t g:=by unfold f; ext1 x; rfl }
    have hw : DifferentiableAt ℝ (play p T) R:= (travel_smooth ..).differentiable (by simp) _
    have hh := hw.hasFDerivAt.comp_hasDerivAt t (hit F t)
    let V:=fderiv ℝ (play p T) R
    change HasDerivAt _ (V (F*R)) t at hh
    have hq := (show HasFDerivAt (play p T) V (L 1) from (show L 1=R from one_mul _).symm ▸ hw.hasFDerivAt).comp 1 L.hasFDerivAt
    rw [show play p T ∘ L = play p U from rfl] at hq
    have hh': V (F*R)=differ p U F:= congr_arg (fun z:Motor G→L[ℝ]ℂ=>z F) (hq.unique (differ_hit ..))
    rwa [hh',H] at hh
  simpa only [Function.comp_apply,whip0,play, motor_one] using is_const_of_deriv_eq_zero (fun s=>(he s).differentiableAt) (fun s=>(he s).deriv) t 0
lemma negatives {ι:Type*} {g:ι→ℝ} {L:Filter ι} (h:Tendsto g L (𝓝 0)) (he: ∀ᶠ i in L,0<g i): Tendsto
    (fun i=> (g i)⁻¹ • (whip F (-g i)-1)) L (𝓝 (-F)):=by
  let f:=(fun x:ℝ=> whip F (-x))
  have hu: HasDerivAt (fun t:ℝ=> -t) (-1) 0:= (hasDerivAt_id (x:=(0:ℝ))).neg
  have hx: HasDerivAt f (-F) 0:=by
    have he: HasDerivAt (whip F ∘ (fun t:ℝ=>-t)) _ 0 := (hit F (- (0:ℝ))).scomp 0 hu
    simpa [f,Function.comp_def] using he
  have hh : Tendsto g L (𝓝[≠] (0:ℝ)):= tendsto_nhdsWithin_iff.mpr ⟨h,he.mono fun i hi=> hi.ne'⟩
  apply ((hasDerivAt_iff_tendsto_slope.mp hx).comp hh).congr; intro i; simp [f,slope]
end YM.XSpace.Sample
