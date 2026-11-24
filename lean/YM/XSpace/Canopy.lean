import YM.XSpace.Nacre
/-!
# Continuum large-angle essential gain imported from the *native* estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Set Filter MeasureTheory Relief Sail Playpen Tide Lattice Trace Octave Chiral
open scoped Topology ContDiff BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v b:E4}(c:Shade.Cut) (R:Gleam c u v b)
variable (p r m n:P)
local notation "ℓ" => line false
local notation "A" => magnetic false true r p
local notation "ϖ" => field false
abbrev wreath (z x y:Cover):ℝ := ∑ i:Axis,∑ j:Axis, q false r i j * Trail z x y A (ϖ m i) (ϖ n j)
abbrev sweepT (u v b:E4):ℝ :=∑ i:Axis,∑ j:Axis,q false r i j* parts c false true r p (ℓ m i) (ℓ n j) u v b
lemma auric [L.IsCountablyGenerated][NeBot L] (R:Gleam c u v b)(s: Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z b): Tendsto (fun i=> (a i)⁻¹^6*wreath p r m n (x i) (y i) (z i)) L (𝓝 (sweepT c p r m n u v b)):=by
  unfold wreath; simp_rw [Finset.mul_sum]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> ((preps c s X Y Z R (shore false m i) (shore false n j) false true r p).const_mul _).congr fun i=> mul_left_comm ..))
lemma post : ∃ C:ℝ, 0≤C∧∀ (z x y:Cover), 32*pad (x-y)≤ pad (x-z) → ‖wreath p r m n z x y-A (x-z)*curled m n r x y‖ ≤ C* rate 5 (x-z)*rate 1 (x-y):=by
  choose C hC H using fun i j:Axis=> of_probe (bunker false m i) (bunker false n j) (surfD false true r p); refine ⟨∑ i:Axis,∑ j:Axis,‖q false r i j‖*C i j, Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=> mul_nonneg (norm_nonneg _) (hC i j),fun z x y h=>?_⟩; unfold curled wreath; simp_rw [Finset.mul_sum,← Finset.sum_sub_distrib, Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>?_)); rw [mul_left_comm (A _), ← mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (H i j x y z h) (norm_nonneg _)).trans_eq (by ring)
-- geometry can be extremely coarse since gain of a power sufficient
lemma crust (s: Stage L a)(h:distance L a x u)(H:u≠0): ∀ᶠ i in L, ‖u‖/4 ≤ a i *pad (x i) ∧ a i *pad (x i) ≤ 3*‖u‖:=by
  have hu:0<‖u‖:=norm_pos_iff.mpr H; filter_upwards [s.good,s.zero.eventually (ge_mem_nhds hu), h.norm.eventually (le_mem_nhds (half_lt_self hu)),h.norm.eventually (ge_mem_nhds (show ‖u‖<2*‖u‖ by linarith))] with i hi hh hx ht; obtain ⟨he,hv⟩:= Shade.size_actual hi (x i); unfold pad Drama.area; constructor <;> linarith
lemma budget (R:Gleam c u v b)(V:512*‖v-b‖ ≤ ‖v-u‖)(s: Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z b) : ∀ᶠ i in L,32* pad (y i-z i)≤pad (y i-x i)∧ ‖v-b‖/4≤ a i*pad (y i-z i)∧ ‖v-u‖/4≤ a i * pad (y i-x i):=by
  have he:= crust s (value Y X) (sub_ne_zero.mpr (gap c (range_sym c R.uv))); have ho:=gap c R.vb; filter_upwards [he,crust s (value Y Z) (sub_ne_zero.mpr ho), s.good] with i ⟨hi,hh⟩ ⟨ht,hR⟩ hv; exact ⟨(mul_le_mul_iff_right₀ hv).mp (by nlinarith [norm_nonneg (v-b)]),ht,hi⟩
lemma shyness {D:ℝ}(X:Cover)(R:ℝ)(h:0<D)(H:0<R)(he:R/4≤D*pad X)(k:ℕ): D⁻¹^k * rate k X ≤ 4^k * R⁻¹^k:= by rw [rated,← mul_pow,← mul_pow]; have hp:0<pad X:=Drama.included _; gcongr (?_^k); field_simp; linarith
lemma payroll : ∃ D:ℝ,0≤D∧∀ (u v b:E4), Gleam c u v b→512*‖v-b‖≤‖v-u‖→ ‖sweepT c p r m n u v b - surfT false true r p (v-u)*(liftedSign m r n* Maxwell.Green (v-b))‖≤ D*‖v-u‖⁻¹^5*‖v-b‖⁻¹:=by
  obtain ⟨D,hD,H⟩:= post p r m n; refine ⟨D*4^6,by positivity,fun u v b hx hv=>?_⟩; let x:= pier u; let y:= pier v; let z:=pier b; have hU: v-u≠0:= sub_ne_zero.mpr (gap c hx.uv).symm; have hV:v-b≠0:=sub_ne_zero.mpr (gap c hx.vb); have hh:= ((auric c p r m n hx starts (voyage u) (voyage v) (voyage b)).sub ((shines starts (value (voyage v) (voyage u)) hU (charted false true r p)).mul (tune_hari starts (value (voyage v) (voyage b)) hV m n r))).norm; apply le_of_tendsto hh; filter_upwards [budget c hx hv starts (voyage u) (voyage v) (voyage b), starts.good] with i ⟨hi,ht,hz⟩ hp; change 0< i at hp -- parse
  set X:=x i; set Y:=y i; set Z:=z i; change ‖i⁻¹^6*wreath p r m n X Y Z-(i⁻¹^4*A (Y-X))*(i⁻¹^2*curled m n r Y Z)‖≤ _; rw [show i⁻¹^4*A (Y-X)*(i⁻¹^2*curled m n r Y Z)=i⁻¹^6*(A (Y-X)*curled m n r Y Z) by ring,← mul_sub,norm_mul,Real.norm_of_nonneg (by positivity :0≤ i⁻¹^6)]; apply (mul_le_mul_of_nonneg_left (H X Y Z hi) (by positivity : 0≤ i⁻¹^6)).trans; let P:=‖v-u‖; let Q:=‖v-b‖; have hp':0<P:= norm_pos_iff.mpr hU; have hh:0<Q:=norm_pos_iff.mpr hV; calc
   _ = D* (i⁻¹^5*rate 5 (Y-X))*(i⁻¹^1*rate 1 (Y-Z)):=by ring
   _ ≤ D*(4^5*P⁻¹^5)*(4^1*Q⁻¹^1):= mul_le_mul (mul_le_mul_of_nonneg_left (shyness _ _ hp hp' hz _) hD) (shyness _ _ hp hh ht _) (mul_nonneg (pow_nonneg (by positivity) _) (sound ..).le) (by positivity)
   _ = _:=by unfold P Q; ring
end YM.XSpace.Season
