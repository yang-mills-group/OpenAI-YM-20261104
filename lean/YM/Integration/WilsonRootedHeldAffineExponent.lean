import YM.Integration.PhysicalAffineScalarRows
import YM.Integration.WilsonRootedHeldAffineCenter

/-! The original classical affine square, determinant, Haar, and old log stay
    on the same planted field. The individual rooted square keeps its cross term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineExponent
open Function Finset Lattice Wilson RG Tree Pressure Matrix
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Coat Control Window Census Blaze Matter Greenbelt
open Push Push.AbsoluteSums Precision SectorMeasure Oriented
open PhysicalAffineScalarRows
open scoped Topology BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}
  {W s μ C:ℝ}{P:Teller G}{Q:ConnectedActivityE6.Target G P}{o:Target.Order G W}{R:Rep G f}

lemma scalar (X:Coat T F){η r q v E:ℝ}(h:Rotator P L η r q v X)(he:0≤E)
    (cut:∀i,|X.driftM i-WilsonRootedHeldAffineCenter.full X i|≤E)(k:Coat.Target c f G):
    |displacement X k|≤v*E ∧
    |(residual X X.driftM k)^2/2-(residual X (fullCenter X) k)^2/2|≤
      (v*E)*(|(residual X (fullCenter X) k)|+(v*E)/2):=by
  have gap:X.driftM-WilsonRootedHeldAffineCenter.full X= -((X.kernelA-X.plate⁻¹).transpose *ᵥ X.linearBill):=by
    rw [Coat.driftM,WilsonRootedHeldAffineCenter.full,Matrix.transpose_sub,Matrix.sub_mulVec]
    abel
  have price:|displacement X k|≤v*E:= by
    have hm:=invoice h.matrix.1 h.full.hot.le k (X.driftM-WilsonRootedHeldAffineCenter.full X) cut he
    rw [gap,Matrix.mulVec_neg] at hm
    exact hm
  have paid:0≤v*E:=mul_nonneg h.signs.le he
  refine ⟨price,?_⟩
  rw [square_difference]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_div,abs_pow,abs_of_pos (show 0<(2:ℝ) by norm_num)]
  calc
    _≤ (v*E)*|residual X (fullCenter X) k|+(v*E)^2/2:=
      add_le_add (mul_le_mul_of_nonneg_right price (abs_nonneg _))
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) price 2) (by norm_num))
    _= _ := by ring

theorem original (H:Cash W s μ L Q o C T R) (χ:Chi)(V:Config G c)(p:Molecule S)
    (i:Greenbelt.Reserve S)(tag:S.Choices)(y:(Greenbelt.allot i).Slice G):
    let X:=WilsonRootedHeldAffineCenter.held T s o.K χ V p i tag y
    let E:=2*(o.ample*distPay o.eta o.gap o.ample (tubularPrice G L) X.B)*(o.cap*X.t)
    (∀k,|displacement X k|≤o.indexPay*E ∧
      |(residual X X.driftM k)^2/2-(residual X (fullCenter X) k)^2/2|≤
        (o.indexPay*E)*(|residual X (fullCenter X) k|+(o.indexPay*E)/2)) ∧
    (∀w:Signed,∀b:Spot c f,Raw.orientation*X.extracted X.μ w b=
      ∑ a∈parents b, ∑ j:G.ColorIndex, (residual X X.driftM ((w,a),j))^2/2) ∧
    (∀e,|X.condensation e|≤(Fintype.card G.ColorIndex:ℝ)*
      ((o.ample+1)*payE o.eta o.gap o.ample (tubularPrice G L))) ∧
    ∀k z,|X.farLog R o.a Q.table z k|≤H.w k ∧ |X.raiseAir R o.a Q.table z k|≤H.w k:=by
  intro X E
  obtain ⟨manifest,-,-,coor,-⟩:=WilsonRootedHeldAffineCenter.original H χ V p i tag y
  have port:=H.laws.data.localP _ X rfl rfl manifest
  have nonneg:0≤E:=mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg port.sails.scale.fuel.le
    (mul_nonneg port.sails.scale.disc (port.sails.scale.heap X.B))))
    (mul_nonneg H.laws.data.safety.1.le port.sails.room.fiery.le)
  exact ⟨scalar X port.sails nonneg coor,retained X H.laws.data.funds.funds,
    X.postedBase port.sails port.empty,(H.quotes _ X rfl rfl manifest).2.1⟩

end YM.Integration.WilsonRootedHeldAffineExponent
