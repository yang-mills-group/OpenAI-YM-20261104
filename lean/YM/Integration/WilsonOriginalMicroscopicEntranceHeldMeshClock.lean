import YM.Integration.WilsonMeasuredPublicEntranceMeshClock

/-! The physical ratio of the very same two meshes pays the complete held j-to-f clock, including the boundary j=f. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldMeshClock
open Function Lattice Wilson RG PhysicalNext.Repeat.Legato
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
open WilsonMeasuredPublicEntranceMeshClock (allowance nonneg)
theorem original {j f:ℕ}(before:j≤f)(apron:ℕ)(window:(C).S.a j/(C).S.a f≤(H f)^apron):
    let Cj:=allowance apron
    (((f-j:ℕ):ℝ)≤Cj*(1+Real.log (H f))) ∧
    (((f-j:ℕ):ℝ)≤Cj*(1+Real.log (H f))^4):=by
  intro Cj
  have pos:0<Real.log (2:ℝ):=Real.log_pos (by norm_num)
  have hot:=((C).path.levels.fits.delayed f).le
  have lp:=Real.log_nonneg hot
  have times:((f-j:ℕ):ℝ)*Real.log 2≤(apron:ℝ)*Real.log (H f):=by
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le before
    have size:(((C).S.steps j n).val:ℝ)=(C).S.a j/(C).S.a (j+n):=by
      rw [Schedule.a,Schedule.a,Schedule.den_add,PNat.mul_coe,Nat.cast_mul]
      have paid:0<(((C).S.denominator j).val:ℝ):=by exact_mod_cast ((C).S.denominator j).property
      field_simp [paid.ne']
    have mesh:(2:ℝ)^n≤(((C).S.steps j n).val:ℝ):=by
      exact_mod_cast WilsonReflectedOriginalPrefixMesh.dyadic (C).S j n
    have measured:=Real.log_le_log (pow_pos (by norm_num:0<(2:ℝ)) n) ((mesh.trans_eq size).trans window)
    simpa only [Real.log_pow,Nat.add_sub_cancel_left] using measured
  have byClock:((f-j:ℕ):ℝ)≤Cj*Real.log (H f):=by
    calc _≤((apron:ℝ)*Real.log (H f))/Real.log 2:=(le_div_iff₀ pos).2 times
         _=Cj*Real.log (H f):=by dsimp [Cj,allowance];ring
  have linear:((f-j:ℕ):ℝ)≤Cj*(1+Real.log (H f)):=by
    exact byClock.trans (mul_le_mul_of_nonneg_left (by linarith) (nonneg apron))
  refine ⟨linear,linear.trans (mul_le_mul_of_nonneg_left ?_ (nonneg apron))⟩
  have high:=pow_le_pow_right₀ (show (1:ℝ)≤1+Real.log (H f) by linarith) (show 1≤4 by decide)
  simpa only [pow_one] using high


end YM.Integration.WilsonOriginalMicroscopicEntranceHeldMeshClock
end
