import YM.Integration.WilsonIndependentCollarOpticalRoom
import YM.Integration.WilsonIndependentCollarOpticalElected

/-! Pay the entire age of the moving finite trial in the elected physical units. -/
set_option autoImplicit false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalSpan
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open scoped Topology

theorem steps (S:Schedule) (m d:ℕ):(d:ℝ)*Real.log 2≤S.scale (m+d)-S.scale m:=by
  induction d with
  | zero=>simp
  | succ d ih=>
    have one:Real.log 2≤Real.log (S.block (m+d)).val:=by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (show 2≤(S.block (m+d)).val by have h:=S.block_large (m+d);omega)
    rw [Nat.cast_succ,←Nat.add_assoc,S.scale_succ];linarith only [one,ih]

theorem original {G:Gauge} (R:Run G)(simple:G.Simple)(P:Credit)(A:ℝ)(hA:0≤A)(ε:ℝ)(eps:0<ε):
    let L:=R.family.path.levels
    let H:=L.clock.hatBeta
    ∀ᶠm:ℕ in atTop,∀(e:ℕ)(V:Realm G (e+1) Credit.leanC)(_hm:V.anchor≤ m),
      V.draws=L → V.y=zz L → ∀(d:ℕ)(β:ℝ),H (m+1)/2≤β →
        L.S.scale (m+d)-L.S.scale m≤A*(1+Real.log (H (m+1))) →
        ∃Z:ℝ,PadRank V m (m+d) Z ∧ P.buy Z≤(Real.sqrt β)^ε:=by
  let L:=R.family.path.levels
  have rise:Tendsto L.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (L.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have hb:0<Real.log (2:ℝ):=by positivity
  let B:=1+A+A/Real.log 2
  have one:1≤B:=by dsimp [B];linarith [div_nonneg hA hb.le]
  filter_upwards [WilsonIndependentCollarOpticalRoom.original R simple P B 1 one ε eps,
    rise.eventually_ge_atTop 3,(rise.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 3] with m bill high highNext
  intro e V hm same age d β thermal span
  let t:=1+Real.log (L.clock.hatBeta (m+1))
  let Δ:=L.S.scale (m+d)-L.S.scale m
  have time:=steps L.S m d
  have duration:(d:ℝ)≤A/Real.log 2*t:=by
    rw [div_mul_eq_mul_div,le_div_iff₀ hb];exact time.trans span
  have rise1:L.clock.hatBeta m ≤ L.clock.hatBeta (m+1):=by
    unfold Calendar.hatBeta;gcongr;exact (Gauge.slopeConstant_pos simple).le
    have oneBlock:=steps L.S m 1
    norm_num only [Nat.cast_one,one_mul] at oneBlock;linarith
  have old:1≤L.clock.hatBeta m:=by linarith
  have hot:1≤L.clock.hatBeta (m+1):=old.trans rise1
  have y:V.y m≤t:=by
    rw [age];change 1+Real.log (Real.log (L.clock.hatBeta m))≤1+Real.log (L.clock.hatBeta (m+1))
    have bound:Real.log (Real.log (L.clock.hatBeta m))≤Real.log (L.clock.hatBeta (m+1)):=(Real.log_le_self (Real.log_nonneg old)).trans
      (Real.log_le_log (zero_lt_one.trans_le old) rise1)
    linarith only [bound]
  let Z:=V.y m+Δ+d
  have room:PadRank V m (m+d) Z:=by
    have pre:=PadRank.frugal V hm (Nat.le_add_right m d)
    rw [same,Nat.add_sub_cancel_left] at pre;exact pre
  refine ⟨Z,room,bill β Z thermal ?_ ((V.depth m hm).trans (room.year m le_rfl (by omega)))
    (Real.log_nonneg hot) ?_⟩
  · change 3≤L.clock.hatBeta (m+1) at highNext
    change L.clock.hatBeta (m+1)/2≤β at thermal;linarith
  · rw [pow_one];change V.y m+Δ+d≤B*t
    dsimp [B];linarith only [y,span,duration]

end YM.Integration.WilsonIndependentCollarOpticalSpan
end
