import YM.Integration.WilsonPositionProgramGaussianConnectedBank
import YM.Integration.WilsonPositionProgramHeatedWallet

/-! A priced complete signed log of two original finite Wilson programs, on a single physical source wallet. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiniteGaussianReturn
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open WilsonPositionProgramFiledGaussianChange WilsonPositionProgramHeatedWallet
open Extra.Trajectories (connected)
open scoped BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

private theorem occupied {r:ℕ}(X:Grade R r)(h:UnitLeading X)(s:R.Mode)(live:s≠R.quiet)(t:Index r):
    (connected X).part (Join.pair s t)=(logMarked X).part (Join.pair s t):=by
  have vac:=congrArg (fun z:Grade R r=>z.part (Join.pair s t)) (log_vacant h)
  change (bottom R r (logVac X)).part (Join.pair s t)=(logVac X).part (Join.pair s t) at vac
  rw [bottom_value,if_neg live] at vac
  rw [log_full h,Poly.part_plus,←vac,zero_add]

theorem original (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){d r:ℕ}(retained:d≤r)
    (w:V→ℝ)(hw:∀v,0<w v)(k:ℕ){base δ:ℝ}(hb:0≤base)(hd:0≤δ)(σ:ℝ)
    (diag:∀i,(K.covariance F tag) i i≤σ)
    (intake:∀i z,Poly.toll w (Join.left i.val)*‖Cloud.paint z (drivers K F tag Y A r i)‖≤base*(1+‖z‖)^k)
    (fee:∀i z,Poly.toll w (Join.left i.val)*‖Cloud.paint z (drivers K F tag W A r i-
      drivers K F tag Y A r i)‖≤δ*(1+‖z‖)^k)
    (s:R.Mode)(live:s≠R.quiet):
    Poly.toll w s*‖(d.factorial:ℂ)*((observe R r (logMarked (Bulk.Fk K F tag W A r)) d).part s-
      (observe R r (logMarked (Bulk.Fk K F tag Y A r)) d).part s)‖ ≤
      δ*WilsonPositionProgramGaussianConnectedBank.price (Board R r) (Precision.Key F G) σ (1+base+δ) k
          (Join.pair s (pick r d)) := by
  let pp:=drivers K F tag W A r
  let qq:=drivers K F tag Y A r
  let B:=1+base+δ
  have one:1≤B:=by dsimp [B];linarith
  have q(i:Hot (Board R r))(z:Precision.Key F G→ℝ):Poly.toll (deployed w r) i.val*‖Cloud.paint z (qq i)‖≤B*(1+‖z‖)^k:=by
    rw [billed]
    exact (intake i z).trans (mul_le_mul_of_nonneg_right (by dsimp [B];linarith) (by positivity))
  have miss(i:Hot (Board R r))(z:Precision.Key F G→ℝ):Poly.toll (deployed w r) i.val*‖Cloud.paint z (pp i-qq i)‖≤δ*(1+‖z‖)^k:=by
    rw [billed]; exact fee i z
  have p(i:Hot (Board R r))(z:Precision.Key F G→ℝ):Poly.toll (deployed w r) i.val*‖Cloud.paint z (pp i)‖≤B*(1+‖z‖)^k:=by
    let a:=Poly.toll (deployed w r) i.val
    have pa:0≤a:=(Poly.worth (WilsonPositionProgramHeatedWallet.positive w hw) i.val).le
    have tri:=mul_le_mul_of_nonneg_left (norm_sub_le (Cloud.paint z (pp i)-Cloud.paint z (qq i)) (-Cloud.paint z (qq i))) pa
    have sq:=miss i z
    rw [map_sub] at sq
    have baseq:=intake i z
    rw [←billed w i.val] at baseq
    have r0:0≤(1+‖z‖)^k:=by positivity
    have step:a*‖Cloud.paint z (pp i)‖≤a*‖Cloud.paint z (pp i)-Cloud.paint z (qq i)‖+a*‖Cloud.paint z (qq i)‖:=by
      simpa only [sub_neg_eq_add,sub_add_cancel,norm_neg,mul_add] using tri
    exact step.trans ((add_le_add sq baseq).trans (by dsimp [B];nlinarith))
  have bound:=WilsonPositionProgramGaussianConnectedBank.original (K.covariance F tag) (K.positive F tag)
    (K.symm F tag) σ diag (deployed w r) (WilsonPositionProgramHeatedWallet.positive w hw) pp qq k one hd p q miss
    (Join.pair s (pick r d))
  rw [billed,Join.left_pair] at bound
  rw [mul_sub,observed (x:=logMarked (Bulk.Fk K F tag W A r)) s retained,
    observed (x:=logMarked (Bulk.Fk K F tag Y A r)) s retained,
    ←occupied _ (Bulk.fk_unit K F tag W A r) s live,←occupied _ (Bulk.fk_unit K F tag Y A r) s live]
  simpa only [Bulk.Fk,Assembly.prescription,pp,qq,drivers,Cloud.shift_zero,zero_add] using bound

end YM.Integration.WilsonPositionProgramFiniteGaussianReturn
end
