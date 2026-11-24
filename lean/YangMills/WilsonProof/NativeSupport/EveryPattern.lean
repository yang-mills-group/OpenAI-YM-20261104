import YangMills.WilsonProof.NativeSupport.SmallPeriodReading

/-! Endpoint comparison at all original periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

theorem every_pattern {I : Type} [Fintype I] [DecidableEq I] (R : Run G)
    (simple : G.Simple) {k N per : ℕ} (T : Slices R.family.path.levels per) (hk : k<N)
    (F : I → Config G (R.family.side N per) → ℝ) (a : I → Site (R.family.side N per)) (s : ℕ)
    (cont : ∀ i,Continuous (F i)) (sym : ∀ i,GaugeInvariant (F i))
    (unit : ∀ i U,|F i U| ≤ 1) (loc : ∀ i,LocalOn (halo s {a i}) (F i))
    (v : ℕ → ℝ) {D η ε : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η) (hε : 0<ε) (small : ε ≤ 1/4)
    (top : v (traversal T hk.le).depth=0)
    (offset : ∀ j,0<j → j<(traversal T hk.le).depth → |v j| ≤ η)
    (L : ℕ) (posL : 0<L)
    (room : Fintype.card I*logLoss R k N (s+scale (traversal T hk.le)*Fintype.card I)+D ≤ L)
    (budget : let d:=traversal T hk.le
      let m:=Fintype.card I
      let χ:=max (charge m (spacing (R.alloy.B.a.budget k).B L)) (m^4)
      (m:ℝ)*Real.exp (-2*D)+(χ:ℝ)*(2*(d.depth:ℝ)*(scale d:ℝ)^4*4*(η*(R.alloy.B.a.clock.kernel.penalty*2))) ≤ ε^2) :
    let d:=traversal T hk.le
    let β:=RGComparison.Core16.line R.family.path per k N
    let W:=fun U=>∏ i,F i U
    |mean d (WilsonUniformUnmarkedInletSignedResponse.line β v 1) W 1-mean d β W 1| ≤ 3*ε := by
  intro d β W
  let m:=Fintype.card I
  let χ:=charge m (spacing (R.alloy.B.a.budget k).B L)
  let K:=2*(d.depth:ℝ)*(scale d:ℝ)^4*4*(η*(R.alloy.B.a.clock.kernel.penalty*2))
  have price : 0 ≤ K := by have hp:=R.alloy.B.a.clock.kernel.penalty_pos; dsimp [K]; positivity
  have total : (m:ℝ)*Real.exp (-2*D)+((max χ (m^4):ℕ):ℝ)*K ≤ ε^2 := budget
  by_cases large : m ≤ (R.family.side k per).val
  · apply original_pattern R simple T hk F a s cont sym unit loc large v hD hη hε small top offset L posL room
    exact (add_le_add_right (mul_le_mul_of_nonneg_right
      (show (χ:ℝ)≤((max χ (m^4):ℕ):ℝ) by exact_mod_cast le_max_left χ (m^4)) price) _).trans total
  have contW : Continuous W := continuous_finsetProd _ fun i _=>cont i
  have symW : GaugeInvariant W := fun g U=>prod_congr rfl fun i _=>sym i g U
  have unitW (U) : |W U| ≤ 1 := by
    change |∏ i,F i U| ≤ 1; rw [abs_prod]
    exact prod_le_one (fun _ _=>abs_nonneg _) (fun i _=>unit i U)
  have direct:=small_reading T hk.le β v contW symW unitW (le_of_not_ge large) top hη offset
  have pay : ((m^4:ℕ):ℝ)*K ≤ ε^2 :=
    (mul_le_mul_of_nonneg_right
      (show ((m^4:ℕ):ℝ) ≤ ((max χ (m^4):ℕ):ℝ) by exact_mod_cast le_max_right χ (m^4)) price).trans
      ((le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg m) (Real.exp_pos _).le)).trans total)
  refine direct.trans (le_trans (le_of_eq ?_) (pay.trans ?_))
  · change η*(((d.depth*((m*scale d)^4*4):ℕ):ℝ)*((R.alloy.B.a.clock.kernel.penalty*2)*(2*1)))=_
    dsimp only [K]; push_cast; ring
  · nlinarith only [hε,small,sq_nonneg (ε-1/4),mul_nonneg hε.le (show 0≤1/4-ε by linarith)]

end YM.Integration.InletSusceptibility.Packet
