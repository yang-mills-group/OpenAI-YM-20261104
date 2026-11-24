import YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution
import YM.Integration.WilsonOriginalMicroscopicEntranceDeposits
import YM.Integration.WilsonThermometerOccupiedLinear

/-! Restore every occupied field's original scalar charge once at the common, unnormalized older receiver. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCohortUnscale
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {I:Type*} {N p f u:ℕ}
local notation "X" t:max => Config G (R.family.side t p)
local notation "P" => R.family.path.rep N p f
def product {T:Type*}(s:Finset I)(A:I→T→ℂ)(U:T):ℂ:=∏a∈s,A a U

theorem salary {T:Type*}[MeasurableSpace T](s:Finset I)(A:I→T→ℂ)(data:∀a,funded (A a)):funded (product s A):=by
  choose M bound using fun a=>(data a).2
  refine ⟨s.measurable_fun_prod (fun a _=>(data a).1),∏a∈s,M a,?_⟩
  intro U
  rw [product,norm_prod]
  exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>bound a U)

private theorem scaled {K t:ℕ}(live:K≤N)(step:t≤K)(F:X K→ℂ)(paid:funded F)(c:ℂ)(W:X t):
    actualTransport R.family (N:=N) (fun U=>c*F U) step W=c*actualTransport R.family (N:=N) F step W:=by
  obtain ⟨m,M,bound⟩:=paid
  let H:=fun U:X K=>(R.family.path.rep N p K).eval U • F U
  have bill:Integrable H (prior G _):=by
    have known:=actualTransport_weighted_integrable R.family R.makes live m.aestronglyMeasurable bound (le_rfl:K≤K)
    rwa [actualTransport_base R.family R.makes live] at known
  have input:(fun U=>(R.family.path.rep N p K).eval U • (c*F U))=c • H:=by
    funext U
    exact smul_comm _ c (F U)
  unfold actualTransport
  rw [input,scale R c H bill step]
  exact smul_comm _ c _

theorem held (live:f≤N)(height:u≤f)(s:Finset I)(A:I→X N→ℂ)(fund:∀a,funded (A a))
    (φ:I→X f→ℂ)(soft:Integrable (fun U=>((P).eval U:ℂ)*product s φ U) (prior G _))
    (χ:I→ℝ)(positive:∀a,0<χ a)(W:X u):
    let c:ℂ:=∏a∈s,(χ a:ℂ)
    let full:=actualTransport R.family (N:=N) (product s A) live
    let charged:=fun U=>((P).eval U) • actualTransport R.family (N:=N) (product s (fun a U=>(χ a:ℂ)⁻¹*A a U)) live U
    let paid:=product s (fun a U=>(χ a:ℂ)*φ a U)
    actualTransport R.family (N:=N) (fun U=>full U-paid U) height W=
      c*(readingAt R (N:=N) charged height W-readingAt R (N:=N) (fun U=>((P).eval U:ℂ)*product s φ U) height W):=by
  intro c full charged paid
  have nz:c≠0:=Finset.prod_ne_zero_iff.mpr (fun a _=>Complex.ofReal_ne_zero.mpr (positive a).ne')
  let cheap:=fun U=>((P).eval U:ℂ)*product s φ U
  have reshape:product s (fun a U=>(χ a:ℂ)⁻¹*A a U)=fun U=>c⁻¹*product s A U:=by
    funext U
    simp only [c,product,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  have a₁:(fun U=>(P).eval U • full U)=c • charged:=by
    funext U
    simp only [full,charged,reshape,Pi.smul_apply,smul_eq_mul,Complex.real_smul]
    rw [scaled R (le_refl N) live (product s A) (salary s A fund) c⁻¹ U]
    field_simp [nz]
  have a₂:(fun U=>(P).eval U • paid U)=c • cheap:=by
    funext U
    simp only [paid,c,product,Finset.prod_mul_distrib,cheap,Complex.real_smul,Pi.smul_apply,smul_eq_mul]
    ring
  obtain ⟨mf,M,bound⟩:=salary s A fund
  have b₁:Integrable (fun U=>(P).eval U • full U) (prior G _):=
    actualTransport_weighted_integrable R.family R.makes (le_refl N) mf.aestronglyMeasurable bound live
  have hF:Integrable charged (prior G _):=by
    rw [a₁] at b₁
    have drop:=b₁.smul c⁻¹
    simpa only [smul_smul,inv_mul_cancel₀ nz,one_smul] using drop
  have b₂:Integrable (fun U=>(P).eval U • paid U) (prior G _):=a₂.symm ▸ soft.smul c
  have read_scale (F:X f→ℂ)(hf:Integrable F (prior G _)):
      readingAt R (N:=N) (c • F) height W=c*readingAt R (N:=N) F height W:=by
    unfold readingAt
    rw [scale R c F hf height]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  calc
    _=actualTransport R.family (N:=N) full height W-actualTransport R.family (N:=N) paid height W:=
      congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes live b₁ b₂ height) W
    _=readingAt R (N:=N) (c • charged) height W-readingAt R (N:=N) (c • cheap) height W:=by
      unfold actualTransport readingAt
      rw [a₁,a₂]
      simp only [Complex.real_smul,Complex.ofReal_inv]
    _=_:=by rw [read_scale charged hF,read_scale cheap soft,mul_sub]

end YM.Integration.WilsonSeparatedPrefixCohortUnscale
end
