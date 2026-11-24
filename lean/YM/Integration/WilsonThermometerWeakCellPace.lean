import YM.Integration.WilsonThermometerWeakPositionMoments

/-! Physical clearance after moving a fixed number of dates toward the coarser mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCellPace
open Filter Set Lattice RG Source Next.Extract WilsonMeasuredAdmission PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "Lev" => R.family.path.levels
local notation "S" => R.family.S

theorem span (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(m b:ℕ)(fits:b ≤ m):
    (S).a (m-b)≤(S).a m*(Real.log (mast (Lev) m))^b:=by
  have pos:0≤Real.log (mast (Lev) m):=Real.log_nonneg (mast_gt_one (Lev) m).le
  induction b with
  | zero=>simp
  | succ b prev=>
    let i:=m-(b+1)
    have idx:i+1=m-b:=by dsimp only [i];omega
    have step:(S).a i=(S).a (m-b)*((S).block i).val:=by
      rw [←idx]
      exact ((eq_div_iff (by exact_mod_cast ((S).block i).property.ne')).mp ((S).a_step i)).symm
    have cl:((S).block i).val ≤ Real.log (mast (Lev) m):=by
      refine (slow.2 i).trans (Real.log_le_log (mast_pos (Lev) i) ?_)
      exact mast_monotone (Lev) simple (Nat.sub_le ..)
    change (S).a i≤_
    rw [step,pow_succ,←mul_assoc]
    exact mul_le_mul (prev (by omega)) cl (by positivity) (by positivity [(S).a_pos m])

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (b v:ℕ)(vp:0<v)(δ:ℝ)(dp:0<δ):
    ∀ᶠ r:ℝ in 𝓝[>] 0,let m:=WilsonMeasuredWindow.stop (Lev) simple v r
      b ≤ m ∧ (S).a (m-b)≤δ*r:=by
  have growth:Tendsto (mast (Lev)) atTop atTop:=
    tendsto_atTop_mono (fun m=>by change WilsonAdmissionScale.logarithm (Lev) m ≤ 2+WilsonAdmissionScale.logarithm (Lev) m;linarith)
      (WilsonAdmissionScale.logarithm_tendsto (Lev) simple)
  have small:∀ᶠ m:ℕ in atTop, (Real.log (mast (Lev) m))^b≤δ*mast (Lev) m:=by
    filter_upwards [growth.eventually ((Real.isLittleO_pow_log_id_atTop (n:=b)).bound dp)] with m h
    have low:=Real.log_nonneg (mast_gt_one (Lev) m).le
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg low b),abs_of_pos (mast_pos (Lev) m)] using! h
  have time:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v vp
  filter_upwards [self_mem_nhdsWithin,time.eventually small,time.eventually_ge_atTop b] with r positive fee hi
  let m:=WilsonMeasuredWindow.stop (Lev) simple v r
  refine ⟨hi,?_⟩
  have mp:mast (Lev) m ≤ mast (Lev) m^v:=by
    simpa only [pow_one] using pow_le_pow_right₀ (mast_gt_one (Lev) m).le (show 1≤v by omega)
  calc
    (S).a (m-b) ≤ (S).a m*Real.log (mast (Lev) m)^b:=span R simple slow m b hi
    _ ≤ (S).a m*(δ*mast (Lev) m):=mul_le_mul_of_nonneg_left fee ((S).a_pos _).le
    _ = δ*((S).a m*mast (Lev) m):=by ring
    _ ≤ δ*r:=mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left mp ((S).a_pos _).le).trans (WilsonMeasuredWindow.stop_spec (Lev) simple v positive)) dp.le

end YM.Integration.WilsonThermometerWeakCellPace
end
