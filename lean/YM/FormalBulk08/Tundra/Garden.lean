import YM.FormalBulk08.Tundra.Halo
import YM.FormalBulk08.Spigot.Road
import Mathlib.Analysis.PSeries

/-! Export at polynomial address revenues. Charge HERE one END closure loss,
finite & local. Keep chosen bigger u in long transfers. Inputs reporting
window applications use full kernels at polynomial charge. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm Avenue Spigot MeasureTheory
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X I: Type}{D m u r:ℕ} {A C σ:ℝ}
lemma cold_border {μ:Halo D}(u:ℕ)(h:0≤A) (hp:Fleet μ)(i:Brush D):(1+A)^u*(μ i).real Set.univ ≤ Spigot.stub μ u A 0 i:= by
    have hh:=hp i; let f(t:Pier):= rush u 0 (A+‖t.val‖)
    have hf : Continuous f:=by unfold f rush;fun_prop
    have he: Integrable f (μ i):=hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f); have hw:= integral_mono (integrable_const (rush u 0 A)) he fun x=> rush_more u h (le_refl _) (show A ≤ A+‖(x:Pier).val‖ by simp); simpa only [f,Spigot.stub,rush, zero_mul,Real.exp_zero,mul_one,integral_const, smul_eq_mul,mul_comm ((μ i).real _)] using hw
lemma penmanship {μ ν:chain (Biglot I) r→Halo D}{f:Studio D→Tile (Biglot I) r}(h:Kme μ ν u 0 A f)(x:I)(p:Studio D): Knoxville (grain (fame _) 1) u (0,x) (f p) (Real.exp u * ((2^u*‖p‖) * A)):= by
   let B (i):ℝ:= (1+(acres i:ℝ))^u * district (μ i) (ν i); let P i:= burse u (acres i) 0 (μ i) (ν i); let C:= 2^u*‖p‖; have hC:0≤C:=by unfold C; positivity
   have hh i: B i≤ P i:= by unfold B P Spigot.district burse; rw [Finset.mul_sum]; simp_rw [mul_add]; exact Finset.sum_le_sum fun j _=> add_le_add (cold_border _ (Nat.cast_nonneg _) (h.plus _) j) (cold_border _ (Nat.cast_nonneg _) (h.minus _) j)
   have hp(v):gauge u 1 (herb (fame _) (0,x) v)*‖f p v‖ ≤ C*P v:= by
       rw [h.code];apply le_trans _ (mul_le_mul_of_nonneg_left (hh v) hC); let U:=herb (fame _) (0,x) v; have ht : Real.exp 0 * gauge u 1 U≤ 2^u*(1+(acres v:ℝ))^u:=by
          have hz : (U:ℝ)≤ 2*acres v:= by unfold U;exact_mod_cast barn_small v x
          unfold Sable.gauge;rw [Real.exp_zero,one_mul, NNReal.coe_one,one_mul, ←mul_pow];apply pow_le_pow_left₀ (by positivity); linarith
       rw [Real.exp_zero,one_mul] at ht; exact (mul_le_mul ht (record_prices (h.plus _) (h.minus _) p) (norm_nonneg _) (by positivity)).trans_eq (show _=C*B v from by unfold C B;ring)
   have he:= (sum_tier (B:=C*A) (f:=fun v:chain (Biglot I) r=> gauge u 1 (herb (fame _) (0,x) v)*‖f p v‖) (g:=fun i=>C*P i) ⟨fun i=>mul_nonneg hC (h.earn.1 i), h.earn.2.1.mul_left C, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.earn.2.2 hC⟩ (fun i=>mul_nonneg (gauge_low ..) (norm_nonneg _)) hp)
   exact back_grain (mul_nonneg hC ((tsum_nonneg h.earn.1).trans h.earn.2.2)) he.2.1 he.2.2

lemma pol_int : Summable (fun i:ℤ=> ((1+(i.natAbs:ℝ))^2)⁻¹):= by
    have he : Summable (fun i:ℕ=>(((↑(i+1):ℝ))^2)⁻¹):= (summable_nat_add_iff 1 (f:=fun i:ℕ=>( (i:ℝ)^2)⁻¹)).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
    apply summable_int_iff_summable_nat_and_neg.mpr; constructor <;> simpa [add_comm (1:ℝ)] using he
abbrev tang (i:ℕ) (j: ℕ):ℝ:= ((1+(i:ℝ))^j)⁻¹
lemma pol_cov [Fintype I]: Summable fun x:Biglot I=>tang (size x.1) 8:= by
   have h:Summable fun x:Cover=>tang (size x) 8:= by
       have hh:= Palm.tenspay (m:=4) (fun (_:Axis) (i:ℤ)=> tang i.natAbs 2) (fun _=> pol_int)
       refine Summable.of_nonneg_of_le (fun x=>inv_nonneg.mpr (by positivity)) (fun x=>?_) hh
       let L:ℝ:= 1+(size x:ℝ); have hl:0<L:=by unfold L; positivity
       have he(i:Axis): (x i).natAbs≤ size x:= Finset.single_le_sum (f:=fun j:Axis=>(x j).natAbs) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)
       have hp(i:Axis): (L^2)⁻¹ ≤ ((1+(↑((x i).natAbs):ℝ))^2)⁻¹:= (inv_le_inv₀ (pow_pos hl _) (pow_pos (by positivity) _)).2 (pow_le_pow_left₀ (by positivity) (add_le_add_right (by exact_mod_cast (he i)) _) _)
       refine le_trans ?_ (Finset.prod_le_prod (s:=Finset.univ) (fun i _=> show 0≤(L^2)⁻¹ from by positivity) (fun i _=> hp i)); simp only [Finset.prod_const, Finset.card_univ]; change (L^8)⁻¹ ≤ ((L^2)⁻¹)^4; rw [inv_pow,←pow_mul]
   have hh:= Summable.mul_of_nonneg (f:=fun x:Cover=>tang (size x) 8) (g:=fun _:I=> (1:ℝ)) h (hasSum_fintype _).summable (fun x=> by unfold tang; positivity) (fun _=>zero_le_one);simpa only [mul_one] using hh
lemma pol_c [Fintype I] (o:I): Summable (fun x:chain (Biglot I) r=>tang (herb (fame _) (0,o) x) (8*r)):= by
    refine Summable.of_nonneg_of_le (fun i=>inv_nonneg.mpr (by positivity)) (fun i=>?_) (Palm.tenspay (fun j (x:Biglot I)=>tang (size x.1) 8) (fun _=> pol_cov)); let L:ℝ:=1+(herb (fame _) (0,o) i:ℝ); have hl:0<L:=by unfold L; positivity
    have ht(j:Fin r):size (i j).1≤herb (fame _) (0,o) i:=by
       have he:= reached (fame I) (Fin.cons (0,o) i) j.succ 0; simpa [fame,capD,herb] using he
    have hp(j:Fin r):(L^8)⁻¹ ≤ ((1+(↑(size (i j).1):ℝ))^8)⁻¹:= (inv_le_inv₀ (pow_pos hl _) (pow_pos (by positivity) _)).2 (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (ht j)) _) _)
    refine le_trans ?_ (Finset.prod_le_prod (f:=fun _=> (L^8)⁻¹) (fun j _=>by positivity) (fun j _=>hp j));simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; unfold tang;rw [inv_pow,←pow_mul]
lemma reunions [Fintype I](u:ℕ)(o:I):∃ C:ℝ,0≤C ∧∀ (f:Studio D→ₗ[ℝ]Tile (Biglot I) r) (B:ℝ), 0≤B →(∀ p, Knoxville (grain (fame _) 1) (↑(u+8*r):ℝ) (0,o) (f p) (B*‖p‖)) → ∃ μ ν,Kme μ ν u 0 (C*B) f:= by
   let n:=u+8*r
   let H (i:chain (Biglot I) r):ℕ:=herb (fame _) (0,o) i
   let h(i:chain (Biglot I) r):= tang (H i) (8*r); have hu: Summable h:=pol_c o;let V:=∑' i,h i;have hv i : 0≤h i:=by unfold h tang;positivity
   let M:ℝ:= Fintype.card (Brush D);let E:ℝ:= (r+10:ℝ)^u; have hE:0≤E:=by unfold E; positivity
   refine ⟨M * E * V,mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hE) (tsum_nonneg hv),fun f B hB hF=>?_⟩
   let G x:= (LinearMap.proj x) ∘ₗ f; let W x:=B*tang (H x) n
   have hw i: 0≤W i:= mul_nonneg hB (by unfold tang; positivity)
   have hh i p:‖G i p‖ ≤ W i*‖p‖:= by
      have he :gauge n 1 (H i)*‖f p i‖≤B*‖p‖:= (Summable.le_tsum (particle (hF p)).2.1 i (fun i _=> mul_nonneg (gauge_low ..) (norm_nonneg _))).trans (particle (hF p)).2.2
      simp only [_root_.YM.FormalBulk08.Sable.gauge,NNReal.coe_one,one_mul] at he; refine le_trans ((le_div_iff₀ (by positivity)).mpr ((Eq.trans_le (mul_comm _ _) he): ‖f p i‖*((1+(H i:ℝ))^n) ≤ _)) (le_of_eq ?_); unfold W tang;ring
   choose μ ν hμ hν hp ht using fun i=> address_account (W i) (hw i) (G i) (hh i)
   let C (i):= burse u (acres i) 0 (μ i) (ν i)
   have hz:0≤ E*M*B:= mul_nonneg (mul_nonneg hE (Nat.cast_nonneg (Fintype.card (Brush D)))) hB
   have hZ i:C i≤h i * (E*M* B):= by
      have hf : 1+((acres i:ℝ)+8) ≤ (r+10:ℝ)*(1+H i):= by
          have he: (acres i:ℝ) ≤ (r+1:ℝ)*H i:=by exact_mod_cast acres_barn i o
          linarith [show 0≤(r:ℝ) by positivity,show 0≤(H i:ℝ) by positivity]
      apply (burse_hot u (show 0≤(acres i:ℝ) from Nat.cast_nonneg _) le_rfl (hμ _) (hν _)).trans; unfold rush;rw [zero_mul, Real.exp_zero,mul_one]; refine (mul_le_mul (pow_le_pow_left₀ (by positivity) hf u) (hp i) (district_pos _ _) (by positivity)).trans_eq ?_; change _^u * (M*(B* ((1+(H i:ℝ))^n)⁻¹))= _
      unfold n h E tang;rw [mul_pow,pow_add, mul_inv]; let x:ℝ:=1+(H i:ℝ);have hh:0<x:=by unfold x; positivity
      field_simp
   exact ⟨μ,ν,hμ,hν,sum_tier ⟨fun i=>mul_nonneg (hv _) hz,hu.mul_right _,by rw [tsum_mul_right]; exact le_of_eq (show V*(E*M*B)=_ from by ring)⟩ (fun i=>burse_below u (Nat.cast_nonneg _) (hμ _) (hν _)) hZ,fun p i=> ht i p⟩
end YM.FormalBulk08.Tundra
