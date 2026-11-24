import YM.Integration.WilsonMacroscopicRichMeasuredFiling
import YM.Integration.WilsonPhysicalExteriorFrame

/-! Engineering and physical running-coupling prices for the one fixed macroscopic hearing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchCurrency
open Set Filter Real Spec PhysMS Pert.Asymptotics OPE RG16 RG16.Literal Lattice Wilson
open Trace.Pilot
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

theorem mesh {I:Type}(h:ℕ){B η M ρ σ:ℝ}(bp:0≤B)(sp:0≤σ)(m:ℕ)(x:I → Cover)
    (data:Tuple C M η B m ρ x):0<C.S.a m*ρ ∧
    (C.S.a m)^h*exp (-σ*C.S.scale m)≤(C.S.a m*ρ)^((h:ℝ)+σ):=by
  have base:1≤Lambda C.path.levels m:=by unfold Lambda;linarith [Real.log_nonneg (C.path.levels.fits.delayed m).le]
  have paid:1≤ρ:=(Real.one_le_rpow base bp).trans data.lo
  have ap:=C.S.a_pos m
  have ar:C.S.a m≤C.S.a m*ρ:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left paid ap.le
  refine ⟨ap.trans_le ar,?_⟩
  have angle:exp (-σ*C.S.scale m)=(C.S.a m)^σ:=by
    change exp (-σ*log (C.S.a m)⁻¹)=_
    rw [Real.log_inv,Real.rpow_def_of_pos ap]
    congr 1;ring
  rw [angle,←Real.rpow_natCast,←Real.rpow_add ap]
  exact Real.rpow_le_rpow ap.le ar (add_nonneg (Nat.cast_nonneg h) sp)

private theorem frame (F:Final C f S)(J:ℝ→tower S)(leading:Leading F J)(h:ℕ){θ:ℝ}(tp:0<θ):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀z:S.Field h,‖(J r h).symm z‖≤A*r^(-(h:ℝ)-θ)*‖z‖:=by
  obtain ⟨K,hK,small⟩:=WilsonPhysicalExteriorFrame.between F h J leading θ tp
  obtain ⟨a,ap,outer⟩:=(RG17.positiveLength.and small).exists
  let t:=-(h:ℝ)-θ
  let D:=(J a h).symm.toLinearMap.toContinuousLinearMap
  let A:=K/(a^t)*‖D‖
  have kp:0≤K:=zero_le_one.trans hK
  have powpos:0<a^t:=Real.rpow_pos_of_pos ap _
  refine ⟨A,mul_nonneg (div_nonneg kp powpos.le) (ContinuousLinearMap.opNorm_nonneg D),?_⟩
  filter_upwards [RG17.positiveLength,(show ∀ᶠ r:ℝ in trail,r≤a from
    (ge_mem_nhds ap).filter_mono nhdsWithin_le_nhds)] with r rp ra z
  have shift:=outer (r/a) ⟨div_pos rp ap,(div_le_one ap).mpr ra⟩ z
  rw [div_mul_cancel₀ _ ap.ne'] at shift
  have one:‖(J a h).symm z‖≤‖D‖*‖z‖:=D.le_opNorm z
  refine shift.trans ((mul_le_mul_of_nonneg_left one (mul_nonneg kp (Real.rpow_nonneg (div_nonneg rp.le ap.le) _))).trans_eq ?_)
  change K*(r/a)^t*(‖D‖*‖z‖)=A*r^t*‖z‖
  rw [Real.div_rpow rp.le ap.le]
  dsimp only [A];ring

theorem normalized (F:Final C f S)(J:ℝ→tower S)(leading:Leading F J)(h:ℕ)
    {s δ:ℝ}(space:δ<s)(K:ℝ){g:ℝ→ℝ}(running:Coupling G g)(simple:G.Simple)(q:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠr in trail,∀y z:S.Field h,‖y-z‖≤K*r^((h:ℝ)+s)→
      ‖y-z‖≤ε*g r^q*r^((h:ℝ)+δ) ∧
      ‖(J r h).symm y-(J r h).symm z‖≤ε*g r^q*r^δ:=by
  let θ:=(s-δ)/2
  have tp:0<θ:=by unfold θ;linarith
  have room:0<s-θ-δ:=by unfold θ;linarith
  obtain ⟨A,nn,price⟩:=frame F J leading h tp
  filter_upwards [price,subpower_payment running simple K (s-δ) (sub_pos.mpr space) ε ep q,
    subpower_payment running simple (A*K) (s-θ-δ) room ε ep q,RG17.positiveLength] with r size raw normed rp y z bill
  have direct:r^((h:ℝ)+s)=r^(s-δ)*r^((h:ℝ)+δ):=by rw [←Real.rpow_add rp];congr 1;ring
  have moving:r^(-(h:ℝ)-θ)*r^((h:ℝ)+s)=r^(s-θ-δ)*r^δ:=by
    rw [←Real.rpow_add rp,←Real.rpow_add rp];congr 1;ring
  constructor
  · rw [direct,←mul_assoc] at bill
    exact bill.trans (mul_le_mul_of_nonneg_right raw (Real.rpow_nonneg rp.le _))
  · rw [←map_sub]
    calc
      _ ≤ A*r^(-(h:ℝ)-θ)*‖y-z‖:=size (y-z)
      _ ≤ A*r^(-(h:ℝ)-θ)*(K*r^((h:ℝ)+s)):=mul_le_mul_of_nonneg_left bill (mul_nonneg nn (Real.rpow_nonneg rp.le _))
      _ = (A*K)*(r^(-(h:ℝ)-θ)*r^((h:ℝ)+s)):=by ring
      _ = (A*K*r^(s-θ-δ))*r^δ:=by rw [moving];ring
      _ ≤ ε*g r^q*r^δ:=mul_le_mul_of_nonneg_right normed (Real.rpow_nonneg rp.le _)

end YM.Integration.WilsonMacroscopicRichWatchCurrency
