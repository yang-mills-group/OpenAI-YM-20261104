import YM.Integration.WilsonPositionProgramNestedLengths
import YM.Integration.WilsonReflectedPublicOpticalJoint

/-! The number of true original transfers in an optical collar on the
previously chosen variable-block schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOpticalDuration
open Function Filter Real Lattice Wilson RG Source Precision RG16 PhysicalNext.Repeat.Legato Marker
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "α" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

theorem blocks (paid:WilsonPositionProgramNestedLengths.Nested R.rolls) :
    Tendsto (fun i:ℕ=>log ((R.family.S.block i).val:ℝ)) atTop atTop :=by
  obtain ⟨h,_,agenda⟩:=paid
  have lower (j:ℕ):j≤(R.rolls.L j).val:=by
    have size:0<h j:=Nat.zero_lt_of_lt (Nat.lt_of_succ_le (agenda j).1)
    have factorial:=Nat.le_of_dvd (Nat.factorial_pos (h j)) (Nat.dvd_factorial size (le_rfl (a:=h j)))
    rw [(agenda j).2]
    change j≤3^(h j).factorial
    exact (Nat.le_succ j).trans ((agenda j).1.trans (factorial.trans
      ((Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left (by decide : 2≤3) _))))
  have many:=R.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)
  apply Real.tendsto_log_atTop.comp
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono _ many
  intro j
  change R.alloy.B.a.clock.J (j+1) ≤ (R.family.S.block j).val
  exact (lower _).trans_eq (congrArg Subtype.val (Push.PriceCompiler.block_eq R.alloy.B.valid j).symm)

theorem original (simple:G.Simple)(paid:WilsonPositionProgramNestedLengths.Nested R.rolls) (A:ℕ)
    {ε:ℝ}(positive:0<ε): ∀ᶠ j:ℕ in atTop, ∀ f:ℕ, j≤f → α j / α f ≤ (β f)^A →
      ((f-j:ℕ):ℝ) ≤ ε*log (β f) :=by
  let price:=((A:ℝ)+1)/ε
  have pos:0<price:=div_pos (by positivity) positive
  obtain ⟨j₀,each⟩:=eventually_atTop.mp ((blocks R paid).eventually_ge_atTop price)
  have rise:Tendsto β atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  obtain ⟨j₁,warm⟩:=eventually_atTop.mp (rise.eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (max j₀ j₁)] with j late f fj moved
  have good:1≤β f :=warm f (by omega)
  have positiveβ:0<β f:=zero_lt_one.trans_le good
  have ages (n:ℕ):(n:ℝ)*price ≤ R.family.S.scale (j+n)-R.family.S.scale j :=by
    induction n with
    | zero=>simp
    | succ n past=>
      have room:=each (j+n) (by omega)
      rw [←Nat.add_assoc,R.family.S.scale_succ,Nat.cast_succ,add_mul,one_mul]
      linarith only [room,past]
  have geometry:=ages (f-j)
  rw [Nat.add_sub_of_le fj] at geometry
  have ratio:=log_le_log (div_pos (R.family.S.a_pos j) (R.family.S.a_pos f)) moved
  rw [log_div (R.family.S.a_pos j).ne' (R.family.S.a_pos f).ne',log_pow] at ratio
  simp only [Schedule.scale,log_inv] at geometry
  apply (mul_le_mul_iff_left₀ pos).mp
  have unit: ε*log (β f)*price = ((A:ℝ)+1)*log (β f) :=by
    dsimp [price]; field_simp
  rw [unit]
  linarith only [geometry,ratio,log_nonneg good]

end YM.Integration.WilsonReflectedPublicOpticalDuration
end
