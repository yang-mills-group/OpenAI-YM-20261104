import YM.Integration.WilsonEmittedAngularJointFare

/-! Use the numerical angular rows of two original colored banks on their
actual dated kinetic changes to price the whole mixed differential. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonEmittedFiledThermalGerm
open Function Finset Lattice Wilson RG Marker RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.FVAAlt2 RegulatorIR.Diagram Comparison.RG02 Comparison.RG02.Adjacent
open WilsonIndependentCapturedAngularWinding WilsonIndependentCapturedFiledDirections
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n : Side} {L : Type} [DecidableEq L] {M : Census L}
local notation "E" => Stationary.Link G n
local notation "I" => SiteSlot G n

def field (clock : UnitCost) (V : Bulk.Colors M G n) (u : L) (z : ℝ×(E)) : ℂ :=
  ((clock.rating z.1)^V.power (Booth.Arm.pub u))⁻¹ •
    Bulk.projected (V.mark (Booth.Arm.pub u)) (clock.enter z.1,Stationary.arm G n 1 z.2)

theorem smooth (clock : UnitCost) (V : Bulk.Colors M G n) (u : L) (funded : Bulk.Well V) :
    ContDiffAt ℝ ω (field clock V u) 0 := by
  let path := fun z:ℝ×(E)=>(clock.enter z.1,Stationary.arm G n 1 z.2)
  have at0 : path 0=0 := by simp [path]
  have regular : ContDiffAt ℝ ω path 0 := by
    exact (clock.here.comp 0 contDiffAt_fst).prodMk ((Stationary.arm G n 1).contDiff.contDiffAt.comp 0 contDiffAt_snd)
  have dial : ContDiffAt ℝ ω (fun z:ℝ×(E)=>clock.rating z.1) 0 := clock.smooth.comp 0 contDiffAt_fst
  have chart : ContDiffAt ℝ ω (Bulk.projected (V.mark (Booth.Arm.pub u))) (path 0) := by
    rw [at0]; exact (funded.suppose_mark (Booth.Arm.pub u)).smooth
  exact (((dial.pow _).inv (by simp [clock.origin])).smul (chart.comp 0 regular))

theorem ray (clock : UnitCost) (V : Bulk.Colors M G n) (u : L) (funded : Bulk.Well V) (e : ℕ) (a:E) :
    Tensor.diagonal (Tensor.coeff (field clock V u) (V.power (Booth.Arm.pub u)+e) 0) (1,a) =
      RegulatorIR.FVAAlt2.Pipeline.See.noseC M u clock V e (Stationary.arm G n 1 a) := by
  let line := (ContinuousLinearMap.id ℝ ℝ).smulRight ((1:ℝ),a)
  have whole : (field clock V u) ∘ line=Booth.Arm.shineM clock V u (Stationary.arm G n 1 a) := by
    funext t
    simp [field,line,Booth.Arm.shineM,Bulk.projected,Integral.sample]
  have compare := Assembly.jet_continuous_right line (f:=field clock V u)
    ((smooth clock V u funded).of_le (show (V.power (Booth.Arm.pub u)+e:ℕ)≤(ω:WithTop ℕ∞) from le_top)) (1:ℝ)
  rw [whole] at compare
  change Assembly.jet (field clock V u) _ (1,a)=Assembly.jet (Booth.Arm.shineM clock V u _) _ 1
  simpa only [line,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul] using compare.symm

private theorem difference (A B: Ranked (I)) (d:ℕ) (a:E) :
    value A d a-value B d a = WilsonEmittedAngularJointFare.held
      (fun r x=>((A r x-B r x:ℝ):ℂ)) (fun (v:E) i=>(v i:ℂ)) d a := by
  simp only [value,packed,render,word,WilsonEmittedAngularJointFare.held,map_sum,map_mul,map_prod,
    MvPolynomial.eval_C,MvPolynomial.eval_X,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,
    Complex.ofReal_sub,sub_mul,sum_sub_distrib]

theorem original (V Z : Bulk.Colors M G n) (c₁ c₂ : UnitCost) (u:L)
    (left : Bulk.Well V) (right : Bulk.Well Z) (A B:Orders (I)) {p e toll:ℕ} (he : e ≤ p)
    (sameV: V.power (Booth.Arm.pub u)=toll) (sameZ : Z.power (Booth.Arm.pub u)=toll)
    (issued:Booth.Arm.Single c₁ V A u p toll) (scheduled:Booth.Arm.Single c₂ Z B u p toll) :
    let d:=e+toll
    let b:=(fun r (x:Tuple (I) r)=>((A e r x-B e r x:ℝ):ℂ))
    ‖iteratedFDeriv ℝ d (field c₁ V u-field c₂ Z u) 0‖ ≤
      (d.factorial:ℝ)*Planned.AtomRegular.polarCost d*(WilsonEmittedAngularJointFare.mass b d*2^d) := by
  intro d b
  have v:ContDiffAt ℝ d (field c₁ V u) 0 := (smooth _ _ _ left).of_le le_top
  have z:ContDiffAt ℝ d (field c₂ Z u) 0 := (smooth _ _ _ right).of_le le_top
  apply WilsonEmittedAngularJointFare.germ _ (v.sub z) b (fun (y:E) i=>(y i:ℂ))
    (fun y i=>by rw [Complex.norm_real]; exact norm_le_pi_norm y i)
  intro a
  have issued_at := YM.Integration.WilsonEmittedFiledThermalGerm.ray c₁ V u left e a
  have schedule_at := YM.Integration.WilsonEmittedFiledThermalGerm.ray c₂ Z u right e a
  have income (c:UnitCost) (P:Bulk.Colors M G n) (T:Orders (I)) (receipt:Booth.Arm.Single c P T u p toll) :
      RegulatorIR.FVAAlt2.Pipeline.See.noseC M u c P e (Stationary.arm G n 1 a)=value (T e) d a := by
    have witnessed : RegulatorIR.FVAAlt2.Pipeline.See.noseC M u c P e (Stationary.arm G n 1 a)=
      Booth.Uniforms.cuff T toll e (Stationary.arm G n 1 a) := receipt.earned e he _
    rw [witnessed,Booth.Uniforms.cuff,Binding.flavor_lo]
    rfl
  have vgrade: V.power (Booth.Arm.pub u)+e=d := by rw [sameV]; dsimp [d]; omega
  have zgrade: Z.power (Booth.Arm.pub u)+e=d := by rw [sameZ]; dsimp [d]; omega
  rw [vgrade,income _ _ _ issued] at issued_at
  rw [zgrade,income _ _ _ scheduled] at schedule_at
  have split : Tensor.diagonal (Tensor.coeff (field c₁ V u-field c₂ Z u) d 0) (1,a) =
      Tensor.diagonal (Tensor.coeff (field c₁ V u) d 0) (1,a) -
      Tensor.diagonal (Tensor.coeff (field c₂ Z u) d 0) (1,a) := by
    simp only [Tensor.diagonal,Tensor.coeff,iteratedFDeriv_sub_apply v z,smul_sub,_root_.sub_apply]
  change Tensor.diagonal (Tensor.coeff (field c₁ V u-field c₂ Z u) d 0) (1,a)=_
  rw [split,issued_at,schedule_at]
  exact difference _ _ _ _
end YM.Integration.WilsonEmittedFiledThermalGerm
