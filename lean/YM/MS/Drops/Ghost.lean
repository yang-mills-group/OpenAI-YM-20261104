import YM.MS.Drops.Soft
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
-- away fall.Work s-independent.
lemma primary_v (k:List Axis){u:ℝ}(hp:0<u)(d:ℕ): ∃ C:ℝ,0≤C∧∀ z:E4,1≤‖z‖→‖harmon (press k (major u)) z‖ ≤ C/‖z‖^d:= by
    let v:=π^2/u; have hv:0<v:= div_pos (pow_pos Real.pi_pos _) hp
    let f (_:E4):=(π/u)^2; obtain ⟨C,hC,hD⟩:= faded ( f:=f ) ( Spire.rope _ ) hv k d; refine ⟨ C,hC,fun z hz=>?_ ⟩; rw [ takes k ( majorM hp ), show harmon (major u)=fun x:E4=> ((( f*blaze v ) x:ℝ):ℂ) from ?_ ]; swap; · exact funext fun i=> by rw [major_flight hp i]; simp only [f,blaze,v,Pi.mul_apply]; congr 3; ring -- power / >>
    have ht : z≠0:= norm_pos_iff.mp (zero_lt_one.trans_le hz); rw [ echoes k ( f:= f*blaze v ) (fun _ _=> contDiffAt_const.mul (Real.contDiff_exp.contDiffAt.comp _ ( contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt ))) ht, Complex.norm_real ]; rw [le_div_iff₀ ( pow_pos ( norm_pos_iff.mpr ht ) _ ),mul_comm ]; exact hD z hz
variable (L K:Degree G)
local notation "U" => xy (fax L) (fax K)
lemma second_v {u:ℝ}(hp:0<u)(d:ℕ): ∃ C:ℝ,0≤ C∧∀ z:E4,1≤‖z‖→ ‖harmon (fun t:E4=> U (ν t)*major u t) z‖≤ C/‖z‖^d:= by
    choose C hC hB using (fun i j:Axis=> primary_v (raypath L K++[i,j]) hp d); let c : ℝ:= ∑ i,∑ j,C i j; have he i j : C i j ≤ c:= (single_le_sum (fun j _=> hC i j) (mem_univ j)).trans (single_le_sum (fun i _=>sum_nonneg fun j _=>hC i j) (mem_univ i)); have hh:0 ≤ c:=le_trans (hC 0 0) (he _ _)
    refine ⟨4*c,by positivity,fun z hz=>?_⟩; rw [ funext ( front L K ( major u ) ), harmon_feather L K _ (fun i j=> Moment.pressed _ ( majorM hp )) ]; unfold paints; split; swap; · change ‖(0:ℂ)‖≤_; rw [norm_zero]; positivity
    rw [Pi.smul_apply,norm_smul]; simp only [norm_pow,norm_neg,norm_one,one_pow,one_mul]; rw [ mul_div_assoc ]; exact sparse_heat _ _ _ _ _ _ fun i j=> (hB i j z hz).trans (div_le_div_of_nonneg_right (he i j) (pow_nonneg (norm_nonneg _) d))
lemma born0 (d:ℕ): ∃ C:ℝ,0≤ C∧∀ z:E4,1≤‖z‖→ ‖γX L K z 0 - ( ↑(Prayer.gleam L K z) :ℂ)‖≤ C/‖z‖^d:= by
    let r:= Pay 0; let a(w:E4):= U ( ν w )*liturgy r w; let b(w:E4):=U (ν w)* major r w; obtain ⟨C,hC,hD⟩:= heat_perturbed L K (pay_positive 0) d; obtain ⟨A,hA,hL⟩:= second_v L K (pay_positive 0) d; refine ⟨C+A,add_nonneg hC hA,fun w hw=>?_ ⟩; have he: γX L K w 0=harmon a w +harmon b w := by rw [γX, Radian.wind,Radian.wind,Radian.wind, ← integral_add ( listener _ ( downE L K ( passion (pay_positive 0 ) )|>.integral ) w ) ( listener _ (( downE L K ( majorM ( pay_positive 0 ) ) ).integral) w ) ]; refine integral_congr_ae (lit_ae.mono ?_); intro z hz; dsimp only; simp_rw [ lease_s L K _ _ hz,Real.exp_zero,one_pow,one_smul,mul_add ] -- a f defin
    have hv : a=HeatP r L K:= funext (front L K (liturgy r)); rw [he, hv, add_sub_right_comm,add_div ]; exact ( norm_add_le .. ).trans ( add_le_add ( hD w hw ) ( hL w hw ) )
-- global bound by leased at zero
lemma global : ∃ C:ℝ,0≤C∧∀ w,‖γX L K w 0‖≤C:= by
    let S:= fun x:E4=>‖wearΦ L K 0 x‖; have h(w:E4)(p:E4): ‖Radian.wave w p*wearΦ L K 0 p‖ = S p:= by simp [S];
    refine ⟨ ∫ p,S p,integral_nonneg fun i=> norm_nonneg _,fun w=>?_ ⟩; rw [ γX,Radian.wind ]; apply (norm_integral_le_integral_norm ..).trans_eq; simp_rw [h]
end YM.MS.Drops
