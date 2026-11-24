import YM.X.Haze.Voucher
/-!
# DCT gate for local kernels including lift choices. One inverse-cube majorant at origin. Uniform over full sequences. χ can be absorbed. Terminal zero lemma too.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print
open scoped Topology BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{f:Mist V}
def Starboard(q:ℕ+)(R:ℝ)(f:Mist V):Prop:= ∀ᶠ i in Fℕ,∀ z, f i z≠0→ street z≤gate q R i
-- for DCT
lemma axis_int : Integrable ((ball (0:E4) R).indicator (fun x:E4=>‖x‖⁻¹^3)):=(integrable_indicator_iff measurableSet_ball).2 (integrableOn_ball_of_norm_le_rpow (by simp : 1≤Module.finrank ℝ E4) (α:=3) (by norm_num [E4]) (C:=1) (Eventually.of_forall fun q:E4=> by rw [Real.rpow_neg (norm_nonneg q),show (3:ℝ)=((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast, Real.norm_of_nonneg (by positivity),inv_pow]; exact (one_mul _).symm.le) (by fun_prop))
lemma outfit (hr:R≥0) (x:E4){z:Cover} (he: index (ε k) x=z)(h:street z≤gate q R k):x∈ball (0:E4) (R+5)∧ ‖x‖≤4*ε k*day z:= by
   let t:= ε k; have ht:= voxel_near x (epsilon_pos q k); rw [he,dist_eq_norm,norm_sub_rev] at ht; have hz:=(norm_sub_norm_le x (spot t z)).trans ht; have hy:= epsilon_pos q k; constructor
   · rw [mem_ball,dist_zero_right]; have hu : t≤1:= by unfold t epsilon; exact inv_le_one_of_one_le₀ (Interval.cane q k)
     unfold t at hu hz; linarith [gate_range R hr z h]
   unfold day; have he:= spot_cost (q:=q) (k:=k) z; unfold t at hz; nlinarith [Nat.cast_nonneg (α:=ℝ) (street z)]
lemma mosaic_dom (hx:R≥0)(h:Visa q R 1 (-3) f)(he:Starboard q R f):∃ c:ℝ,c≥0∧ ∀ᶠ i in Fℕ, ∀ᵐ x:E4, ‖((ε i)^(-4:ℤ)) • mosaic (ε i) (f i) x‖≤c*((ball (0:E4) (R+5)).indicator (fun x:E4=>‖x‖⁻¹^3) x):= by
    obtain ⟨C,hc,hw⟩:=h.who; refine ⟨C*4^3,by positivity,?_⟩; filter_upwards [he,hw] with i hi hh; filter_upwards [Measure.ae_ne volume (0:E4)] with x hz; let z:=index (ε i) x
    set j:=ε i; have hp:0<j:=epsilon_pos ..; have ht:= day_pos z; have hg : 0< ‖x‖:= norm_pos_iff.mpr hz; unfold mosaic; by_cases hu:f i z=0; · rw [show f i _=0 from hu,smul_zero,norm_zero]; exact mul_nonneg (by positivity) (indicator_nonneg (fun y _=> by positivity) _)
    obtain ⟨hb,hX⟩:= outfit hx x rfl (hi z hu); rw [indicator_of_mem hb, norm_smul,Real.norm_of_nonneg (zpow_pos hp _|>.le)]; have hy : (j*day z)⁻¹ ≤ 4* ‖x‖⁻¹:= by apply (inv_le_iff_one_le_mul₀ (mul_pos hp ht)).2; field_simp; linarith
    have h': ‖f i z‖ ≤ C*(j*(day z)⁻¹^3):= by simpa only [price,zpow_neg,zpow_natCast, inv_pow,zpow_one,pow_one, zpow_ofNat,j] using! hh z (hi z hu)
    change j^(-4:ℤ)*‖f i z‖ ≤ _; calc
         _ ≤ j^(-4:ℤ)*(C*(j*(day z)⁻¹^3)):= by gcongr
         _ = C*((j*day z)⁻¹)^3:= by rw [mul_inv,zpow_neg,zpow_ofNat]; field_simp
         _ ≤ C*(4* ‖x‖⁻¹)^3:=by gcongr
         _ = _:=by ring
include hq in
lemma visa_limit_global (hx:R≥0)(h:Visa q R 1 (-3) f)(he:Starboard q R f)(x:E4)(hz:x≠0): Released (fun i=> (ε i ^(-4:ℤ)) • mosaic (ε i) (f i) x):= by
    let z(i):=index (ε i) x; have h₁:= entrant hq x; rcases le_or_gt ‖x‖ R with hR|hR; exact h.whereL x hz hR z h₁ -- zpow δ maybe
    refine ⟨0,tendsto_const_nhds.congr' ?_⟩; filter_upwards [h₁.norm.eventually (lt_mem_nhds hR),he] with i hi hp; change 0= _ • f i (z i); rw [show f i (z i)=0 from not_not.mp (fun h=> not_le_of_gt hi (gate_range R hx _ (hp _ h))),smul_zero] -- neq coercion
section dct
variable [CompleteSpace V]{g:E4→V}{w:ℕ→ Finset Cover}
lemma dom_budget (hx:R≥0)(h:Visa q R 1 (-3) f)(hw:∀ᶠ i in Fℕ,Frugal (f i) (w i))(hp:Starboard q R f)(hg:∀ x:E4,x≠0→Tendsto (fun i=> (ε i ^(-4:ℤ)) • mosaic (ε i) (f i) x) Fℕ (𝓝 (g x))): Tendsto (fun i=>∑ z∈w i,f i z) atTop (𝓝 (∫ x:E4,g x)):= by
    let F(k:ℕ):= (ε k^(-4:ℤ)) • mosaic (ε k) (f k); obtain ⟨C,hC,he⟩:= mosaic_dom hx h hp; have ht:Tendsto (fun i=>∫ x:E4,F i x) Fℕ (𝓝 (∫ x:E4,g x)):= tendsto_integral_filter_of_dominated_convergence (fun x=>C*((ball 0 (R+5)).indicator (fun x:E4=>‖x‖⁻¹^3) x)) (hw.mono fun i hi=> (AEStronglyMeasurable.const_smul (mosaic_ok (epsilon_pos q i) hi).aestronglyMeasurable (ε i^(-4:ℤ)))) he (Integrable.const_mul axis_int C) ((Measure.ae_ne volume (0:E4)).mono (fun x hx=> hg x hx)) -- Measure.ae_ne orientation
    apply ht.congr'; filter_upwards [hw] with i hi; have he:= epsilon_pos q i; change ∫ x:E4,(ε i^(-4:ℤ)) • mosaic _ (f i) x=_; rw [integral_smul,zpow_neg,zpow_ofNat,mosaic_sum he hi,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
include hq in
lemma dom_release (hx:R≥0)(h:Visa q R 1 (-3) f)(hw:∀ᶠ i in Fℕ,Frugal (f i) (w i))(hp:Starboard q R f): Released (fun i=> ∑ z∈ w i,f i z):= by
    let r (x:E4):= if h':x=0 then (0:V) else (visa_limit_global hq hx h hp x h').choose; refine ⟨_,dom_budget hx h hw hp (g:=r) ?_⟩; intro x hh; unfold r; rw [dif_neg hh]; exact (visa_limit_global hq hx h hp x hh).choose_spec
end dct
end YM.PositionX.Haze
