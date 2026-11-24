import YM.AllOrder.Floe.Runner
import YM.WilsonCoeffUV.Step.Rebase

/-! The Laurent weight of every deposited physical row is the same Taylor
coefficient as the independent kinetic change of variable. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCoin
open Function Filter PowerSeries
open PositionX.Jet PertExtension PertExtension.Series
open AllOrder AllOrder.Floe AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Response
open WilsonCoeffUV.Blue
open scoped Topology ContDiff Classical

private theorem packed (A:Cost):PowerSeries.mk (Tested.term A)=A:=by
  ext i
  exact PowerSeries.coeff_mk ..

private theorem power {f:ℝ→ℝ}{A:Cost}{k:ℕ}(hf:Act k f (Tested.term A))(j:ℕ):
    Act k (f^j) (Tested.term (A^j)):=by
  simpa only [xpow,packed] using exact_power hf j

private theorem inverse_square (p:Cost)(unit:constantCoeff p=1):((pace p)⁻¹)^2=p:=by
  let A:=pace p
  let B:=A⁻¹
  have ba:B*A=1:=PowerSeries.inv_mul_cancel A ((pace_cc unit).trans_ne one_ne_zero)
  calc
    B^2=B^2*(p*A^2):=by rw [pace_tax unit,mul_one]
    _=p*(B*A)^2:=by ring
    _=p:=by rw [ba]; simp

/-- The real fitted factor multiplies the unshifted input degree e with the
angular rank r. Only finite Taylor polynomials of the inverse ratio are used. -/
theorem original (p:Cost)(unit:constantCoeff p=1)(e r j:ℕ):
    Pace.ladder (((r:ℝ)-e)/2) (Tested.term (p-1)) j=
      coeff j ((pace p)^e*((pace p)⁻¹)^r):=by
  let A:=pace p
  let B:=A⁻¹
  have ac:constantCoeff A=1:=pace_cc unit
  have ba:B*A=1:=PowerSeries.inv_mul_cancel A (ac.trans_ne one_ne_zero)
  have bc:constantCoeff B=1:=by
    simpa only [map_mul,ac,mul_one,map_one] using congrArg constantCoeff ba
  have square:B^2=p:=inverse_square p unit
  let q:=Tested.term (p-1)
  let L:=Pace.ladder (((r:ℝ)-e)/2) q
  have q0:q 0=0:=by
    simp only [q,Tested.term,coeff_zero_eq_constantCoeff_apply,map_sub,unit,map_one,sub_self]
  have equation:PowerSeries.mk L * B^e=B^r:=by
    ext k
    let f:=delay (Tested.term B) k
    have hf:Act k f (Tested.term B):=Act.swell _ le_rfl
    have f0:f 0=1:=hf.zero.trans (by simpa only [Tested.term,coeff_zero_eq_constantCoeff_apply] using bc)
    have hq:Act k (fun x:ℝ=>f x^2-1) q:=by
      have s:Act k (f^2+(fun _ : ℝ=>-1)) (Tested.term (B^2)+just (-1)) :=
        (power hf 2).add (Act.static (-1:ℝ))
      refine s.repairs (fun i _=>?_ )
      change coeff i (B^2) + just (-1:ℝ) i=coeff i (p-1)
      rw [square,map_sub,coeff_one]
      by_cases z:i=0 <;> simp [just,z,sub_eq_add_neg]
    have hr:=Pace.coin_word (((r:ℝ)-e)/2) hq q0
    have prod:=exact_prod hr (power hf e)
    have near:∀ᶠ x in 𝓝 (0:ℝ), 0<f x:=
      hf.nice.continuousAt (Ioi_mem_nhds (by rw [f0]; norm_num : 0<f 0))
    have reads:((fun x:ℝ=>(1+(f x^2-1))^(((r:ℝ)-e)/2)) * f^e) =ᶠ[𝓝 0] f^r:=by
      filter_upwards [near] with x pos
      change (1+(f x^2-1))^(((r:ℝ)-e)/2) * f x^e=f x^r
      rw [show 1+(f x^2-1)=f x^2 by ring,←Real.rpow_natCast_mul pos.le,
        show ((2:ℕ):ℝ)*(((r:ℝ)-e)/2)=(r:ℝ)-e by ring,
        Real.rpow_sub_natCast pos.ne',Real.rpow_natCast]
      exact div_mul_cancel₀ _ (pow_ne_zero e pos.ne')
    have same:plus L (Tested.term (B^e)) k=Tested.term (B^r) k:=
      (Act.realizes reads prod).trans_at (power hf r) le_rfl
    change coeff k (PowerSeries.mk L * PowerSeries.mk (Tested.term (B^e)))=coeff k (B^r) at same
    rwa [packed] at same
  have all:PowerSeries.mk L=A^e*B^r:=calc
    _=PowerSeries.mk L*(B*A)^e:=by rw [ba,one_pow,mul_one]
    _=A^e*(PowerSeries.mk L*B^e):=by rw [mul_pow]; ring
    _=A^e*B^r:=by rw [equation]
  exact (PowerSeries.coeff_mk ..).symm.trans (congrArg (coeff j) all)

/-- The rank and grade of a legal Wilson curvature prism give exactly the
prefactor in FundedSpringPeriodGerm.packets. -/
theorem deposited (p:Cost)(unit:constantCoeff p=1){rise grade:ℕ}(legal:rise≤grade)(j:ℕ):
    Pace.ladder ((((rise+2:ℕ):ℝ)-grade)/2) (Tested.term (p-1)) j =
      coeff j (p*(pace p)^(grade-rise)):=by
  rw [original p unit]
  let A:=pace p
  let B:=A⁻¹
  have ab:A*B=1:=PowerSeries.mul_inv_cancel A ((pace_cc unit).trans_ne one_ne_zero)
  have erase:A^rise*B^rise=1:=by rw [←mul_pow,ab,one_pow]
  have split:A^grade=A^(grade-rise)*A^rise:=by rw [←pow_add,Nat.sub_add_cancel legal]
  change coeff j (A^grade*B^(rise+2))=_
  rw [split,pow_add,show A^(grade-rise)*A^rise*(B^rise*B^2)=
    A^(grade-rise)*(A^rise*B^rise)*B^2 by ring,erase,mul_one,inverse_square p unit,mul_comm]

end YM.Integration.WilsonVacuumPreResetCoin
