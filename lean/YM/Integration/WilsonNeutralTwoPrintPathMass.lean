import YM.Integration.WilsonNeutralTwoPrintPathSpectrum

/-! On arbitrary ordered finite inputs the actual symmetric mixed pegs cost at
most the original total variation after signed subtraction, at every rank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathMass
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open private packed_rank from YM.Integration.WilsonNeutralTwoPrintPathSpectrum
open scoped Classical BigOperators

private theorem extracted {I:Type} [Fintype I](T:Ranked I)(cap r:ℕ)(hr:r≤cap):
    Lava.marble r (packed T cap)=symmetry (T r):=by
  let U:Ranked I:=fun l=>if l≤cap then symmetry (T l) else 0
  have cropped:Within cap U:=by
    intro l ne
    by_contra h
    exact ne (by simp [U,h])
  have symmetric (l:ℕ):IsSym (U l):=by
    by_cases h:l≤cap
    · simpa only [U,if_pos h] using is_symmetry (T l)
    · change ∀(τ:Equiv.Perm (Fin l)) z,U l (z ∘τ)=U l z
      simp [U,h]
  have exactly:packed U cap=packed T cap:=by
    unfold packed
    apply sum_congr rfl
    intro l hl
    rw [show U l=symmetry (T l) from if_pos (by simpa only [mem_range,Nat.lt_succ_iff] using hl),
      render_symmetry]
  rw [←exactly,packed_rank U cap cropped symmetric r]
  exact if_pos hr

private theorem price {I:Type} [Fintype I]{r:ℕ}(raw:(Fin r→I)→ℂ):
    ∑z,‖((symmetry (fun x=>(raw x).re) z:ℝ):ℂ)+
      ((symmetry (fun x=>(raw x).im) z:ℝ):ℂ)*Complex.I‖≤∑z,‖raw z‖:=by
  let U:=Equiv.Perm (Fin r)
  let n:ℝ:=Fintype.card U
  have positive:0<n:=Nat.cast_pos.mpr Fintype.card_pos
  have val (z:Fin r→I):
      ((symmetry (fun x=>(raw x).re) z:ℝ):ℂ)+
        ((symmetry (fun x=>(raw x).im) z:ℝ):ℂ)*Complex.I=
        (n⁻¹:ℝ) • ∑a:U,raw (z∘a):=by
    simp only [symmetry_at,Complex.ofReal_mul,Complex.ofReal_sum,Complex.real_smul]
    change (n⁻¹:ℝ)*(∑a:U,((raw (z∘a)).re:ℂ))+
      ((n⁻¹:ℝ)*(∑a:U,((raw (z∘a)).im:ℂ)))*Complex.I=_
    rw [mul_assoc,←mul_add,Finset.sum_mul,←Finset.sum_add_distrib]
    simp only [Complex.re_add_im]
  calc
    _ ≤ ∑z,n⁻¹*∑a:U,‖raw (z∘a)‖:=by
      apply sum_le_sum
      intro z _
      rw [val,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr positive.le)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr positive.le)
    _ = _:=by
      rw [←mul_sum,sum_comm]
      have permuted (a:U):(∑z,‖raw (z∘a)‖)=∑z,‖raw z‖:=
        Equiv.sum_comp (Tuple.perm I a) (fun z=>‖raw z‖)
      simp only [permuted,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change n⁻¹*(n*_)=_
      rw [←mul_assoc,inv_mul_cancel₀ positive.ne',one_mul]

variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:Bool→V→ℕ)(s:Hot C)
  (layout:Bool→Layout G)(tape:Bool→Finset Age)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (cost a) (order a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(proper:∀a,Legal (tape a) (layout a))(v:s.val.val)
local notation "pupil" a:max e:max B:max => (peek dvd_rfl (M a) (grades a) (layout a) (tape a) (x a) e B).part s.val
local notation "Slots" => Site n × Loc G 1

include stock positive proper v in
theorem original (e cap:ℕ)(raw:(r:ℕ)→(Fin r→Slots)→ℂ)
    (angular:∀p B,phase p (pupil false e B)-phase p (pupil true e B)=
      MvPolynomial.eval B (packed (fun r z=>phase p (raw r z)) cap)):
    WilsonEmittedAngularJointFare.mass (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) cap≤
      ∑r∈range (cap+1),∑z,‖raw r z‖:=by
  let D:=fun p=>packed (fun r z=>phase p (raw r z)) cap
  have head:=WilsonNeutralTwoPrintPathSpectrum.original M x grades s layout tape stock positive proper v e D angular
  unfold WilsonEmittedAngularJointFare.mass
  apply sum_le_sum
  intro r withinRange
  have hr:r≤cap:=by simpa only [mem_range,Nat.lt_succ_iff] using withinRange
  simp_rw [head]
  dsimp only [D]
  rw [extracted _ cap r hr,extracted _ cap r hr]
  exact price (raw r)

end YM.Integration.WilsonNeutralTwoPrintPathMass
end
