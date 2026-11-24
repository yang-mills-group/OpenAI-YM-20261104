import YM.Integration.WilsonNeutralTwoPrintAccount
import YM.Integration.WilsonConditionalTaylorWheelTensors

/-! The mixed pegs of two independently funded physical prints are the ordered
coefficients of their signed angular polynomial, including rank zero. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathSpectrum
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
local notation "Slots" => Site n × Loc G 1

private theorem packed_rank {I:Type} [Fintype I] (T:Ranked I)(d:ℕ)
    (bound:Within d T)(pure:∀r,IsSym (T r))(r:ℕ):
    Lava.marble r (packed T d)=T r:=by
  have last:still T (d+1):=by
    intro l hl
    by_contra ne
    have :=bound l ne
    omega
  have same:totalR T=packed T d:=by
    rw [visible last,packed]
    apply sum_congr rfl
    intro l _
    change (∑ z:Fin l→I,T l z • ∏ i,MvPolynomial.X (z i))=_
    simp only [render,word,MvPolynomial.smul_eq_C_mul]
  rw [←same]
  exact WilsonConditionalTaylorWheelTensors.rank T ⟨_,last⟩ pure r

variable {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:Bool→V→ℕ)(s:Hot C)
  (layout:Bool→Layout G)(tape:Bool→Finset Age)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (cost a) (order a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(proper:∀a,Legal (tape a) (layout a))(v:s.val.val)
local notation "pupil" a:max e:max B:max => (peek dvd_rfl (M a) (grades a) (layout a) (tape a) (x a) e B).part s.val
local notation "bank" a:max p:max => WilsonNeutralTwoPrintFronts.table (M a) (x a) (grades a) (layout a) (tape a) s (phase p)
local notation "pole" a:max => Launch.index C (grades a) s.val+1
local notation "spectrum" a:max p:max e:max => packed ((bank a p) e) (e+(pole a))

include stock positive proper v in
theorem paid (a p:Bool)(e:ℕ):
    (∀B:Link G n,phase p (pupil a e B)=MvPolynomial.eval B (spectrum a p e)) ∧
    ∀r,Lava.marble r (spectrum a p e)=(bank a p) e r:=by
  have H:=WilsonNeutralTwoPrintFronts.issued (M a) (x a) (grades a) (layout a) (tape a) s
    (phase p) (stock a) (positive a) (proper a) v (allowed p) e e 1 zero_lt_one
  dsimp only at H
  refine ⟨?_,packed_rank _ _ (H.2.1.grade e) (H.2.1.symmetricW e)⟩
  intro B
  apply Complex.ofReal_injective
  rw [←H.2.2.2 e B]
  have read:=H.2.1.earned e le_rfl (Stationary.arm G n 1 B)
  change See.noseC _ _ _ _ e _ = Booth.Uniforms.cuff _ _ e _ at read
  rw [WilsonEmittedFiledDeckFare.row,read,Booth.Uniforms.cuff,Binding.flavor_lo]
  rfl

include stock positive proper v in
theorem original (e:ℕ)(D:Bool→MvPolynomial (Slots) ℝ)
    (angular:∀p B,phase p (pupil false e B)-phase p (pupil true e B)=MvPolynomial.eval B (D p)):
    ∀r (z:Fin r→Slots),WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e r z=
      ((Lava.marble r (D false) z:ℝ):ℂ)+((Lava.marble r (D true) z:ℝ):ℂ)*Complex.I:=by
  have book:=paid M x grades s layout tape stock positive proper v
  have selected (p:Bool):(spectrum false p e)-(spectrum true p e)=D p:=by
    apply MvPolynomial.funext
    intro B
    rw [map_sub,←(book false p e).1,←(book true p e).1]
    apply angular
  have components (p:Bool)(r:ℕ):
      Lava.marble r (D p)=(bank false p) e r-(bank true p) e r:=by
    rw [←selected p]
    change Lava.canyon r (_-_) = _
    rw [map_sub]
    exact congrArg₂ (·-·) ((book false p e).2 r) ((book true p e).2 r)
  intro r z
  rw [components false,components true]
  rfl

include stock positive proper v in
theorem invoice (e cap:ℕ)(D:Bool→MvPolynomial (Slots) ℝ)
    (angular:∀p B,phase p (pupil false e B)-phase p (pupil true e B)=MvPolynomial.eval B (D p))
    (fare:(r:ℕ)→(Fin r→Slots)→ℝ)
    (bound:∀r≤cap,∀z,‖((Lava.marble r (D false) z:ℝ):ℂ)+
      ((Lava.marble r (D true) z:ℝ):ℂ)*Complex.I‖≤fare r z):
    (cap.factorial:ℝ)*WilsonEmittedAngularJointFare.mass
      (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) cap ≤
      (cap.factorial:ℝ)*∑r∈range (cap+1),∑z,fare r z:=by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold WilsonEmittedAngularJointFare.mass
  apply sum_le_sum
  intro r hr
  apply sum_le_sum
  intro z _
  rw [original M x grades s layout tape stock positive proper v e D angular]
  exact bound r (by simpa only [mem_range,Nat.lt_succ_iff] using hr) z

end YM.Integration.WilsonNeutralTwoPrintPathSpectrum
end
