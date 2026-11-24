import YM.Integration.WilsonSingleHardRadius

/-! On the actual one-marker gallery every live regular field contains its unique
root. Its complete regular response has a pointwise bound after the real quiet
vacuum is restored, while its forced partner keeps exactly the original gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Lattice Wilson RG Marker QuadraticLocal Ac
open Push.AbsoluteSums Fusion Fusion.Attached
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {J:Census (Fin 1)} {P:Rep G n} {o:Fin 1→Site n}
variable {T I : Type} {w C d : ℝ}
variable (A: Gallery T I o P J)
local notation "fire" => J.fire 0

theorem light (wp:0<w) (paid:A.Pays (fun _=>w) P.p.supportExponent C d) (t:T) (U:Config G n) :
    w*‖(A.E.log t U).part fire‖ ≤ C := by
  obtain ⟨f,pos,room,fee⟩:=paid.budget.budget
  let price := fun i=>Poly.toll (fun _=>w) (A.E.mode i)*f i
  have money (i:I) : 0≤price i := mul_nonneg (Poly.worth (fun _=>wp) _).le (pos i)
  have root (i:I) : o 0∈A.E.ground i := by
    apply A.E.roots i 0
    rcases cases (A.E.mode i) with quiet|shot
    · exact (A.E.live i quiet).elim
    · rw [shot]
      exact mem_singleton_self _
  have net : SumBudget price C := by
    refine budget_mono (fee (o 0)) money fun i=>?_
    rw [if_pos (root i)]
    exact le_mul_of_one_le_right (money i) (Real.one_le_exp (mul_nonneg P.p.exponent_pos.le (Nat.cast_nonneg _)))
  have cap : Poly.price (fun _=>w) (A.E.log t U) ≤ C := by
    refine (Poly.budgeted (fun _=>wp) net.2.1 (f:=fun i=>A.E.frame i t U) (fun i=>?_)).2.trans net.2.2
    rw [Lamps.frame,Poly.solo]
    exact mul_le_mul_of_nonneg_left
      (A.E.light_size i t U (room i t _ (A.E.address i).anchor)) (Poly.worth (fun _=>wp) _).le
  simpa only [Poly.solo_toll] using (Poly.member (fun _=>wp) fire (A.E.log t U)).trans cap

private theorem pinned {X:Poly J} (quiet:X.part J.quiet=0) : WilsonForcedMarkerLine.pinned 0 X := by
  intro s missing
  rcases cases s with h|h
  · exact h ▸ quiet
  · rw [h] at missing
    exact (missing (mem_singleton_self _)).elim

/-- Square-free extraction on the full original Wilson integrand. -/
theorem release (wp:0<w) (paid:A.Pays (fun _=>w) P.p.supportExponent C d) (t:T) (U:Config G n) :
    (A.density t U).part fire =
      ((P.eval U:ℝ):ℂ)*(A.E.log t U).part fire + ((gallery A.K).density t U).part fire := by
  let e := A.E.log t U
  let gas := A.gas t U
  let x : ℂ := P.activities.gas P.p U
  have eq : e.part J.quiet=0 := A.E.quiet_of_hasSum t U (paid.budget.sums P.p.exponent_pos.le (fun _=>wp) ..)
  have gq : gas.part J.quiet=x := Hard.packet_of_quiet A.K t U
    (Hard.packet_summing A.K paid.wages P.p.exponent_pos.le (fun _=>wp) t U)
  have star : (gas-Poly.bead J x).part J.quiet=0 := by change gas.part J.quiet -(Poly.bead J x).part J.quiet = 0; simp [Poly.bead,gq]
  have nul := WilsonForcedMarkerLine.square (pinned eq) (pinned star)
  have mul : e*gas=x • e := by
    rw [mul_sub] at nul
    rw [show e*gas=e*Poly.bead J x from sub_eq_zero.mp nul,mul_comm,Poly.product_bead]
  have pass : Poly.pass e=1+e := by
    simp [Poly.pass,Finset.sum_range_succ]
  have empty : (gallery A.K).E.log t U=0 := tsum_empty
  change (((↑(Real.exp (P.exponent U)):ℂ) • (Poly.pass e*gas)).part fire)=
    _ + (((↑(Real.exp (P.exponent U)):ℂ) • (Poly.pass ((gallery A.K).E.log t U)*gas)).part fire)
  rw [empty,Next.Rank.Exponential.pass_zero,one_mul,pass,add_mul,one_mul,mul,Poly.part_smul,Poly.part_plus,
    Poly.part_smul,Poly.part_smul,Rep.eval,Complex.ofReal_mul]
  change _= ((Real.exp (P.exponent U):ℝ):ℂ)*x*e.part fire+_
  ring

end YM.Integration.WilsonSingleHardRadius
