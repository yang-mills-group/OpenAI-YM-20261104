import YM.OPE.Short.Vacuum
/-! Support and scalar read in the exact ground discrepancy. `sector` queries
precisely the unit component of the real-split preassigned Reader, not a vacant
phase operator supplied by PT. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Extraction Spec Climb Pert
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives
local notation "gap"=>fun z=> extra (S:=S) (z:=z)
variable {I:Type}[Fintype I]

def scalar (x:I→E4)(v:I→S.Tag)(o:E4):= (upon S 0 o gapPos (voices gap)) (R.fresh 0 x o (voices v))

section
include hG X
lemma scalarizes (x:I→E4)(v:I→S.Tag)(o:E4):scalar U R x v o • S.unit 0 = R.fresh 0 x o (voices v):= vacuum_vector U X hG none o _ gap
lemma identity_formula (x:I→E4)(v:I→S.Tag)(o:E4)(q:Viewers U)(hx:Injective x):formula U R x o (voices v) gapPos (voices gap) 0 q = Orbits.moment (spectator U q) x (voices v) - scalar U R x v o :=by
    unfold formula; rw [tagged U v x q hx]; apply congr_arg (_-·)
    unfold Orbits.trunc; conv_lhs => change ∑ q:Fin 1, ∑ i:R.channels q.val, (_* _:ℂ); rw [Fintype.sum_unique]
    change ∑ c:R.channels 0, _ = scalar U R x v o
    rw [scalar,← R.assemble _ _ _ _,← vacuum_common U X hG (q:=q),map_sum] -- map_sum already maybe
    exact Finset.sum_congr rfl (fun i _=>show _= (upon (spectator U q) 0 o gapPos (voices gap)) (_ • (R.actor _ i)) from ((upon (spectator U q) 0 o gapPos (voices gap)).map_smul (R.coef 0 i x (voices v) o) _).symm)
end
variable (I)
def plate (M η:ℝ): Set (I→E4):={x|WithinRoom 1 M η x 0}

lemma meal (M η:ℝ): IsCompact (plate I M η):=by
    let B(i j:I):= {x:I→E4| η≤ ‖x i-x j‖}
    have h(i j:I):IsClosed (B i j):= isClosed_le continuous_const (by fun_prop)
    have hp: plate I M η=({x:I→E4|∀i,x i∈Metric.closedBall 0 M} ∩ (⋂ (i : I) (j : I) (h:i≠j), B i j)):= by
        ext x
        simp only [plate,B,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_inter_iff, Set.mem_setOf_eq,Metric.mem_closedBall,dist_zero_right,sub_zero,mul_one] -- WithinRoom structure doesn't unfold by simp lemma. need constructor
        exact ⟨fun h=>⟨(by simpa using h.span), (by simpa using h.spaced) ⟩,fun h=>⟨by simpa using h.1, by simpa using h.2⟩⟩
    rw [hp]; exact (isCompact_pi_infinite (fun (_:I)=> isCompact_closedBall ..)).inter_right (isClosed_iInter fun i=>isClosed_iInter fun j=> isClosed_iInter (fun u=> h i j))

variable {I} {M η:ℝ}(hs:0<η)
omit [Fintype I]
include hs
lemma plate_conf(x:I→E4)(hp:x∈plate I M η) : Injective x:=by
    rintro i j h
    exact (Classical.byContradiction fun he=> lt_irrefl (0:ℝ) (by simpa [h] using (show 0<η*1 from by positivity).trans_le (hp.spaced i j he)))
lemma injective_harmonic(x:I→E4)(o:E4)(hp:x∈plate I M η)(k:ℕ): Injective (harmonic (X.r k) x o) := by
    rintro i j h; exact (plate_conf hs x hp (smul_right_injective E4 (X.positive k).ne' (add_right_cancel (b:=o) h)))
lemma fitted {r:ℝ}(hr:0≤ r)(x:I→E4)(o:E4)(hp:x∈plate I M η):WithinRoom r M η (harmonic r x o) o:=by
    have hf (x:E4)(y:E4): ‖r•x+o - (r • y+o)‖=‖x-y‖*r := by rw [add_sub_add_right_eq_sub,← smul_sub, norm_smul_of_nonneg hr, mul_comm]
    refine ⟨fun i=>?_,fun i j he=> le_trans (mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hp.spaced i j he) hr) (hf _ _).symm.le⟩
    unfold harmonic; rw [add_sub_cancel_right,norm_smul_of_nonneg hr,mul_comm]; exact mul_le_mul_of_nonneg_right (by simpa only [sub_zero,mul_one] using hp.span i) hr
end YM.OPE.Short
