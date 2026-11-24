import YM.MSbar.Folia.Montage
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p:ℕ} 
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
open Metric Pressure Push.AbsoluteSums ConnectedActivityE6 Posture
variable (P:Patch)(K: KernelChoices)(J:Voice G) (Q:Palisade) (χ:ChartRatio G) (W':ℝ)
local notation "v!"=>tip G P.L
local notation "H"=> P.L
noncomputable def maxZ (G:Gauge)(Q:Palisade)(x:ℝ):=4*(shade G*rot Q x)
noncomputable def topP (J:Voice G)(Q:Palisade)(x:ℝ):= J.C* (maxZ G Q x)^2
local notation "y!"=> maxZ G Q
variable (g:LocalRatio χ)(h: Clear G J)
include g h
lemma cabin (Q₀:0≤ W') : ∀ᶠ x in atTop, let d:=tip G P.L x; let t:=rot Q d; let v:=maxZ G Q d; let w:=topP J Q d
      v ≤ J.r ∧ v<χ.radius ∧ 2*J.C*v ≤ J.δ ∧ w≤ shade G*t ∧ W'*(w+pillow d)+pillow d+w ≤ room d ∧ W'*(w+pillow d)+pillow d ≤ t:=by
    let q:=-(1/2:ℝ); let m:=tip G P.L; let C:=J.C; let u:=rot Q; let f:=u∘m; let g':=maxZ G Q∘m; let l:=topP J Q∘m; have hv :Rate G P.L q f:= (flog P (G:=G)).mul_left _; have hf: Rate G P.L q g':=(hv.mul_left _).mul_left 4; have hl:Rate G P.L (q+q) l:=(hf.mul hf).mul_left C|>.congr (Eventually.of_forall (fun x=>by change _= C*(maxZ .. * maxZ ..); unfold l topP Function.comp; dsimp only; ring))
    let V:= 4*W'+5; have hp:= g.patch; let m₀:=Real.log ∘ m
    have hF:= Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)
    filter_upwards [shiftedLog G P.L, hF.eventually_ge_atTop (V^2), hf.below (by norm_num [q]) _ h.depth,
       hf.below (by norm_num [q]) _ (half_pos hp), (hf.mul_left (2*C)).below (by norm_num [q]) _ h.dist, hl q (by norm_num [q]), (hF.eventually_ge_atTop 1)] with x hx hg hf hz he hk hu
    let X:=m x; have hX:0 < X:= zero_lt_one.trans hx.2.2.1; let a:= X^q; have ha:0<a:=Real.rpow_pos_of_pos hX _; let b:=Real.log X; have ht: V^2 ≤ b:=hg; have hU:1≤ b:=hu; have hM: l x ≤ a:= (le_abs_self _).trans hk
    let d':=distance X; have he': a ≤ d':=le_mul_of_one_le_right ha.le hU
    have hp':d' ≤ skies X:=le_mul_of_one_le_right ((ha.trans_le he').le) hU; have hS:skies X ≤ u X:= (le_mul_of_one_le_left (ha.le.trans (he'.trans hp')) ?_); swap
    · have he:0 ≤ ceilingP Q:=by unfold ceilingP; positivity
      linarith only [he]
    have ht : V ≤ Real.sqrt b:=by nlinarith only [Real.sqrt_nonneg b,Real.sq_sqrt (zero_le_one.trans hU),ht]
    have hvw: l x≤ d':= hM.trans he'; have hvb:0≤ l x:=mul_nonneg (zero_le_one.trans h.cost) (sq_nonneg _)
    intro d t v w; refine ⟨(le_abs_self _).trans hf,lt_of_le_of_lt ((le_abs_self _).trans hz) (half_lt_self hp),(le_abs_self _).trans he,(hvw.trans (hp'.trans hS)).trans (le_mul_of_one_le_left (hvb.trans (hvw.trans (hp'.trans hS))) (shade_one G)), ?_⟩
    have he : W'*(w+pillow X)+pillow X+w ≤ room X:=by
        apply le_trans (b:= V*d') _ ((mul_le_mul_of_nonneg_right ht (hvb.trans hvw)).trans_eq (mul_comm ..)); have hp :w ≤ d':=hvw; have hf :pillow X=3*d':=rfl; unfold V; linarith only [hp,hvb.trans hvw,mul_le_mul_of_nonneg_left hp Q₀,hf,congr_arg (W'*·) hf]
    have hz :Real.sqrt b≤ b:=by nlinarith only [hU,Real.sq_sqrt (zero_le_one.trans hU),Real.sqrt_nonneg b]
    exact ⟨he,(le_add_of_nonneg_right hvb).trans (he.trans ((mul_le_mul_of_nonneg_left hz (hvb.trans hvw)).trans hS))⟩
-- linear copy.Moving taste
variable (x: Positions (Primary c G))(F:Forest S.ratio)
local notation "Zc"=> (tint G (Exterior.Body 1 c) x)
noncomputable def linCash (F:Forest S.ratio)(x: Positions (Primary c G)): F.Free → G.Color := fun i : F.Free=>linearCopy S.ratio (Exterior.collect G (tint G _ x)) i.val
local notation "f!"=> linCash F x
omit g h
lemma clothSize {t:ℝ}(hf:‖x‖ ≤ t) (i : F.Free): ‖linCash F x i‖ ≤ shade G*t:=by
    unfold linCash linearCopy; split; rw [norm_zero]; exact mul_nonneg (shade_pos G|>.le) ((norm_nonneg _).trans hf)
    next hg=> exact (norm_le_pi_norm (tint G _ x) _).trans ((tint_le x).trans (mul_le_mul_of_nonneg_left hf (shade_pos G).le)) -- inferred
lemma sends (i :F.Free) : G.lieExp (linCash F x i)=Precision.replica S.ratio (represent (tint G _ x)) i.val:=by
    have hp:= Precision.exp_copy S.ratio (Zc); rw [←hp]; unfold RG.increment linCash; rw [show (1 : Config G f) i.val=1 from rfl,mul_one]
-- credit realization.
variable (W V:Stage)(cost:Clear G J)(g:LocalRatio χ)
local notation "T'"=> ribbonD
-- conditional posture
end YM.MSbar.Bakery.Film
