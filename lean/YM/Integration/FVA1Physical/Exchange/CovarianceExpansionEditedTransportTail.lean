import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedActionRows
import YM.Next.RANK.Headwater
import YM.Push.ABSOLUTE_SUMS.Path
import YM.Push.LOCAL_SPLITTING.Orientation
import YM.UVNext.PRICED_KERNELS.Basin
import YM.Extra.WILSON_STARTUP.Ownership

/-! A one-bond edit can move a genuine parallel-transport row only through a
slot on the submitted cover path that reaches this actual physical bond. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Set Finset Lattice RG Wilson Precision Push.Local
open private slot_span from YM.Push.ABSOLUTE_SUMS.Path
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem term_bound (P:PathData G)(x:Face (Per n))(i:ℕ)(U:Fld):
    ‖P.ellTerms x i U‖ ≤ |(P.row x.2 i).1| *2:=by
  rw [PathData.ellTerms,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)

private theorem native_row_cap (P:PathData G)(c:Clip){σ C Λ:ℝ}(pay:P.Bounds c σ C Λ)
    (x:Face (Per n))(U:Fld):‖P.ell U x‖ ≤ 2*C:=by
  let b:=fun i:ℕ=>|(P.row x.2 i).1| *Real.exp (σ*((P.row x.2 i).2.length:ℝ))
  have bank:=pay.rows x.2
  have ab:=(P.ell_dominated pay x).absolute U
  have one(i:ℕ):‖P.ellTerms x i U‖≤b i*2:=by
    apply (term_bound P x i U).trans
    apply mul_le_mul_of_nonneg_right _ zero_le_two
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg pay.width.le (Nat.cast_nonneg _)))
  unfold PathData.ell
  exact (norm_tsum_le_tsum_norm ab).trans ((ab.tsum_le_tsum one (bank.2.1.mul_right 2)).trans (by
    rw [tsum_mul_right,mul_comm (2:ℝ) C];exact mul_le_mul_of_nonneg_right bank.2.2 zero_le_two))

/-- True torus distance from the edited bond to the oriented quadratic
center. No winding lift, torus cardinality or count of paths is charged. -/
theorem relocated_row (P:PathData G)(c:Clip){σ C Λ:ℝ}(pay:P.Bounds c σ C Λ)
    (e:Edge (Site n))(U V:Fld)(same:∀l:Edge (Site n),l≠e → U l=V l)(s:Signed)(x:Face (Per n)):
    ‖P.ell (pull s 0 U) x-P.ell (pull s 0 V) x‖≤4*C*Real.exp (-σ*(separation e.1 (turnSites s 0 x.1):ℝ)):=by
  let d:=separation e.1 (turnSites s 0 x.1)
  let b:=fun i:ℕ=>|(P.row x.2 i).1| *Real.exp (σ*((P.row x.2 i).2.length:ℝ))
  let u:=fun i=>P.ellTerms x i (pull s 0 U)
  let v:=fun i=>P.ellTerms x i (pull s 0 V)
  let R:=4*Real.exp (-σ*(d:ℝ))
  have rn:0≤R:=by dsimp only [R];positivity
  have reach(i:ℕ)(move:u i≠v i):d≤(P.row x.2 i).2.length:=by
    by_contra! far
    apply move
    apply Next.Rank.Alarm.steamed P x i
    apply agrees_pull
    intro l seen _
    apply same l
    intro eq
    obtain ⟨a,aa,position⟩:=Finset.mem_image.mp seen
    have ee:turnSites s 0 a=e.1:=by rw [position,eq]
    have dist:d=separation x.1 a:=by dsimp only [d];rw [←ee,turn_sep,separation_comm]
    exact far.not_ge (dist ▸ (slot_span x.1 (P.row x.2 i).2 a aa))
  have ticket(i:ℕ):‖u i-v i‖≤b i*R:=by
    have bn:0≤b i:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    by_cases eq:u i=v i
    · rw [eq,sub_self,norm_zero];exact mul_nonneg bn rn
    have dom:‖u i-v i‖≤4* |(P.row x.2 i).1|:=by
      exact (norm_sub_le ..).trans ((add_le_add (term_bound P x i _) (term_bound P x i _)).trans_eq (by ring))
    have distance:(d:ℝ)≤((P.row x.2 i).2.length:ℝ):=by exact_mod_cast reach i eq
    have amp:1≤Real.exp (σ*((P.row x.2 i).2.length:ℝ))*Real.exp (-σ*(d:ℝ)):=by
      rw [←Real.exp_add];exact Real.one_le_exp (by linarith only [mul_le_mul_of_nonneg_left distance pay.width.le])
    calc
      _ ≤ 4* |(P.row x.2 i).1|:=dom
      _ ≤ (4* |(P.row x.2 i).1|)*(Real.exp (σ*((P.row x.2 i).2.length:ℝ))*Real.exp (-σ*(d:ℝ))):=
        le_mul_of_one_le_right (by positivity) amp
      _ = b i*R:=by dsimp only [b,R];ring
  have bank:=pay.rows x.2
  have ub:=(P.ell_dominated pay x).summable (pull s 0 U)
  have vb:=(P.ell_dominated pay x).summable (pull s 0 V)
  unfold PathData.ell;rw [←ub.tsum_sub vb]
  exact (norm_tsum_le_tsum_norm (ub.sub vb).norm).trans (((ub.sub vb).norm.tsum_le_tsum ticket (bank.2.1.mul_right R)).trans (by
    rw [tsum_mul_right];exact (mul_le_mul_of_nonneg_right bank.2.2 rn).trans_eq (by dsimp only [R,d];ring)))

/-- Difference of the full squares of the independently unmasked numerical
transport row, with its true cover/period summability bill discharged. -/
theorem relocated_square (P:PathData G)(c:Clip){σ C Λ:ℝ}(pay:P.Bounds c σ C Λ)
    (e:Edge (Site n))(U V:Fld)(same:∀l:Edge (Site n),l≠e → U l=V l)(s:Signed)(x:Face (Per n)):
    |(‖P.ell (pull s 0 V) x‖^2-‖P.ell (pull s 0 U) x‖^2)/2|≤
    8*C^2*Real.exp (-σ*(separation e.1 (turnSites s 0 x.1):ℝ)):=by
  let a:=‖P.ell (pull s 0 V) x‖;let b:=‖P.ell (pull s 0 U) x‖
  have av:a≤2*C:=native_row_cap P c pay x _
  have bv:b≤2*C:=native_row_cap P c pay x _
  have sd:|a-b|≤4*C*Real.exp (-σ*(separation e.1 (turnSites s 0 x.1):ℝ)):=
    (abs_norm_sub_norm_le ..).trans ((norm_sub_rev ..).le.trans (relocated_row P c pay e U V same s x))
  have ae:0≤a+b:=add_nonneg (norm_nonneg _) (norm_nonneg _)
  have f:=mul_le_mul sd (add_le_add av bv) ae ((abs_nonneg _).trans sd)
  change |(a^2-b^2)/2|≤_
  rw [sq_sub_sq,abs_div,abs_mul,abs_of_nonneg ae,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [f]

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
