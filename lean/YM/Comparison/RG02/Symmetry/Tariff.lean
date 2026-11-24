import YM.Comparison.RG02.Symmetry.Mouth
import YM.Comparison.RG02.Laplace.Prism
/-!
# The analytically moving aperture (no uniform pricing claim)

 Forge Ward at each geometry via Laplace/Facing and the exact model push. Modify Trial to
 x varying with t, constants sufficient along any such path tending to x₀. Same Fernique estimate
 (no assumption a moving rate). No higher than fixed r needed at a point. This version requires
 only `Tendsto` of x, so may pinch through a complex projector test before varying gauge direction
 (here physical x still real!) -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (w : S.Choices)
  (x : fieldDir G c 1) (p' : ℝ→fieldDir G c 1)
local notation "X"=> fieldDir G c 1
local notation "L"=> Precision.Key F G→ℝ
local notation "μ"=> Gaussian.cloud (K.covariance F w)
local notation "ζ"=> Bulk.translated K F
local notation "T"=> Bulk.Joint S F (G:=G)
private lemma stage : Continuous (Bulk.stage K F):= continuous_const.prodMk (continuous_id.prodMk (fderiv ℝ (K.b F) 0).continuous)
private lemma approaches_path (hp : Tendsto p' along (𝓝 x)) : ∀ᶠ t in along,∀ v:L, ‖ζ (p' t) v‖≤1+‖ζ x v‖∧ room K F (p' t) v ≤ 2*room K F x v := by
  have he : ∀ᶠ t in along, ‖Bulk.stage K F (p' t)-Bulk.stage K F x‖ ≤1 := by
     have he := (((stage K F).continuousAt.tendsto.comp hp).sub (tendsto_const_nhds (x:=Bulk.stage K F x))).norm; rw [sub_self,norm_zero] at he; filter_upwards [he.eventually (gt_mem_nhds zero_lt_one)] with a ha; exact le_of_lt ha
  filter_upwards [he] with t ht v
  have hw : ‖ζ (p' t) v‖ ≤ 1+ ‖ζ x v‖ := by
     rw [show ζ (p' t) v=(Bulk.stage K F (p' t)-Bulk.stage K F x)+ζ x v from (by unfold Bulk.translated Assembly.translate; abel)]; exact (norm_add_le ..).trans (add_le_add ht le_rfl)
  refine ⟨hw,?_⟩; rw [room_cost,room_cost]; linarith only [hw,norm_nonneg (ζ x v)]

private lemma shaded {C:ℝ} (hC:0<C) (x y:T) (h:‖x‖≤1+‖y‖) : Radial.shade (C/2) x ≤ Real.exp C * Radial.shade C y:= by unfold Radial.shade; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [ mul_nonneg hC.le (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) h 2)), mul_nonneg hC.le (sq_nonneg (1-‖y‖))]

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable (W : Bulk.Colors R G f)
variable (c₀ : ℝ) (r : ℕ) (s : R.Mode)
variable (A : ℝ → Set (F.Slice G)) (hW : Bulk.Well W) (hp : Tendsto p' along (𝓝 x))
include hW hp
lemma shadow : ∃ δ:ℝ, 0<δ ∧ ∀ A, Wins K D F p' A δ→ Bill (r+1) (fun g=> (charge μ (drift K F w g (p' g) W (A g) r)).part s) := by
   obtain ⟨c,hc,h⟩:= gauss_translated K F w x; let hα:= Bulk.geometric_ready K F w W hW
   have hz := Assembly.radial_comparison W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) hα (show 0<c/2 from by positivity)
   obtain ⟨δ,C,p,hδ,H,M⟩:= (Assembly.Zonal.remainder _ hz s r).cost
   let v(z:L) := room K F x z ^ p * Radial.shade c (ζ x z)
   have hv(z:L):0≤v z:= mul_nonneg (pow_nonneg (room_pos ..).le _) (Real.exp_pos _).le
   let e : ℝ:=Real.exp c; have he:0≤e:= (Real.exp_pos ..).le
   let f(g:ℝ):= (C*2^p*e)*g^(r+1)
   have hf(g:ℝ)(h:0≤g): 0≤f g:= by unfold f; positivity
   refine ⟨δ,hδ,fun A HA=>?_⟩; apply volume_bill (r+1) s hv (h p) (C*2^p*e) (by positivity)
   filter_upwards [eventually_pos,approaches_path K F x p' hp,HA] with t ht H₀ H₁ z
   unfold drift; by_cases he : z∈scope K F t (p' t) (A t)
   · rw [Set.indicator_of_mem he,Pi.sub_apply, Extra.Trajectories.part_sub]; apply (M (ζ (p' t) z) t ht (H₁.2 z he)).trans
     let u:= room K F (p' t) z; let w':= room K F x z; change C*u^p*_*t^(r+1) ≤ f t*v z
     have hu:= room_pos K F (p' t) z; have hh:= Real.exp_pos ((c/2)*‖ζ (p' t) z‖^2)
     apply le_trans (b:= C*(2*w')^p*(Real.exp c*Radial.shade c (ζ x z))*t^(r+1)); swap
     · unfold f v w' e; rw [mul_pow]; apply le_of_eq; ring
     have hb:=shaded (G:=G) (S:=S) (F:=F) hc _ _ (H₀ z).1; have hr : 0 ≤ C*(2*w')^p := by have hw : 0<w':=room_pos K F x z; positivity
     exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le (H₀ z).2 p) H) hb hh.le hr) (pow_nonneg ht.le _)
   rw [Set.indicator_of_notMem he,Poly.part_nil,norm_zero]; exact mul_nonneg (hf t ht.le) (hv _)

-- At r any, genuine bound with absent support. uses K only for smoothed model.
omit hp in
private lemma invoice : ∃ p:ℕ,∃ C:ℝ,0≤C ∧ ∀ g:ℝ, |g|≤1 → ∀ x:X, ∀ v:L, ‖(desired K F w g x W r v).part s‖ ≤ C*room K F x v^p := by
   let H : T→ PTable R := Assembly.expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F w W)
   let f := Assembly.rows H s
   have hx c (h:0<c):= Assembly.radial_comparison W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) (Bulk.geometric_ready K F w W hW) h
   -- use Prism.budget (Affine RHS, general L) would need all inputs used via finite basis. Simpler read its common elements directly.
   obtain ⟨C,p,hC,H⟩:= Zone.Invoice.fin_sum (Z:=Radial.zone (E:=T)) (range (r+1)) (fun n x=> ‖f n x‖) (fun n _=> ((hx 1 zero_lt_one s).invoice n).norm)
   refine ⟨p,C,hC,fun g h x v=>?_⟩
   rw [show (desired K F w g x W r v).part s=Zone.eval f r g (ζ x v) from Assembly.Zonal.zone_eval ..]
   have he(i:ℕ): ‖g^i • f i (ζ x v)‖ ≤ ‖f i (ζ x v)‖:= by rw [norm_smul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h)
   apply (le_trans (norm_sum_le ..) (sum_le_sum fun i _=>he i)).trans
   have hh:=H (ζ x v); simp_rw [Finset.sum_apply,Real.norm_eq_abs, abs_of_nonneg (show 0≤∑ i∈ Finset.range (r+1), ‖f i (ζ x v)‖ from by positivity)] at hh; exact hh

lemma lighting (k:ℕ) {B : Set (F.Slice G)} (hA : Liberty F A B): Bill k fun t=> (charge μ (removed K F w t (p' t) W (A t) r)).part s:= by
   obtain ⟨d,hd,H⟩:= gauss_translated K F w x
   obtain ⟨p,C,hC,Hc⟩:= invoice K F w W r s hW
   obtain ⟨ε,hε,Hε⟩:= earned K F p' A hA
   let b(y:L):= room K F x y^(p+k)*Radial.shade d (ζ x y)
   have hb(y:L): 0≤b y:= mul_nonneg (pow_nonneg (room_pos ..).le _) (Real.exp_pos _).le
   apply volume_bill k s hb (H (p+k)) (C*2^(p+k)/ε^k) (by positivity)
   filter_upwards [approaches_path K F x p' hp,Hε,eventually_small (show (0:ℝ)<1 from zero_lt_one)] with g hg he hy v
   have ht:=hy.1; by_cases hv:v∈scope K F g (p' g) (A g)
   · unfold removed; rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hv),Poly.part_nil, norm_zero]; exact mul_nonneg (by positivity) (hb _)
   unfold removed; rw [Set.indicator_of_mem (Set.mem_compl hv)]
   let u:= room K F (p' g) v; let l:= room K F x v
   have hu:0<u:=room_pos ..; have hl:0<l:=room_pos ..
   have hz:u≤2*l:=(hg v).2; have ha:=le_trans (he v hv) (mul_le_mul_of_nonneg_left hz ht.le)
   calc
      _ ≤ C * u ^ p := Hc g (by rw [abs_of_nonneg ht.le]; exact hy.2.le) _ _
      _ ≤ C*(2*l)^p := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hz _) hC
      _ ≤ C*(2*l)^p*(g*(2*l)/ε)^k := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by rw [one_le_div hε]; exact ha))
      _ ≤ C*(2*l)^p*(g*(2*l)/ε)^k* Radial.shade d (ζ x v):= le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
      _ = _ := by unfold b l; simp_rw [pow_add,div_pow,mul_pow,div_eq_mul_inv]; ring

-- forge in full motion, comparison pointwise in the chosen geometry. A may be a *moving aperture*.
include D
lemma accost : ∃ B ∈𝓝 (1:F.Slice G), IsOpen B ∧ ∀ A, Liberty F A B →
    Bill (r+1) (fun g=> (portal K F w c₀ W (p' g) A g).part s-(value (g:ℂ) (Bulk.Fk K F w W (p' g) r)).part s) := by
   obtain ⟨δ,H,hδ⟩:= shadow K D F w x p' W r s hW hp; obtain ⟨B,b,he,h⟩:=agree K D F x p' hp H; refine ⟨B,b,he,fun A ha=>?_⟩
   refine bill_congr ?_ (bill_add (hδ A (h A ha)) (bill_neg (lighting K F w x p' W r s A hW hp (r+1) ha)))
   obtain ⟨Z,z,hZ⟩:=ha; filter_upwards [h A ⟨Z,z,hZ⟩,hZ,eventually_pos] with g hg hM hx
   unfold portal; dsimp only [Pi.add_apply,Pi.neg_apply]; rw [one_thermal K F w g c₀ (p' g) W (A g) r (limited K F D g (p' g) w (A g) hg.1 hM.2.1) hx hW,smul_smul, inv_mul_cancel₀ (show _ from Complex.ofReal_ne_zero.mpr (wage_pos K F w g c₀ (p' g) hx).ne'), one_smul, Extra.Trajectories.part_sub, Poly.part_plus]; abel
end YM.Comparison.RG02.Symmetry
