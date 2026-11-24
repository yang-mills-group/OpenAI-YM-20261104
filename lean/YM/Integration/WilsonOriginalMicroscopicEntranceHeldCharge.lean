import YM.Integration.WilsonOriginalMicroscopicEntranceHeadCharge
import YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution

/-! Exact per-face refund of the nominated microscopic public weights at every held field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldCharge
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedGridSchool WilsonOriginalMicroscopicGuardedPage
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonOriginalMicroscopicGuardedTrial (guarded)
open Function Finset Filter MeasureTheory Lattice Wilson RG OPE.Therm Marker
open WilsonOriginalMicroscopicEntranceEarlier (salary face)
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonOriginalMicroscopicEntranceGridRow (pin old)
open WilsonOriginalMicroscopicEntranceGridStock (old_paid)
open WilsonOriginalMicroscopicEntranceHeadCharge (amount field)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (d:Fin 3→ℕ) {N p f n:ℕ} (live:f+n≤N)
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)
local notation "fk" => Nat.le_add_right f n
local notation "P" => R.family.path.rep N p f
variable (Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
local notation "originalSource" => old R d ((fk).trans live) Y o

private theorem read_scale {j:ℕ} (jf:j≤f)(c:ℂ)(F:X f→ℂ)(hf:Integrable F (prior G _))(W:Config G (R.family.side j p)):
    readingAt R (N:=N) (c • F) jf W=c*readingAt R (N:=N) F jf W:=by
  unfold readingAt
  rw [scale R c F hf jf]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem original (χ:Fin 3→ℝ)(positive:∀a,0<χ a)(s:(J).Mode)(F:X f→ℂ)
    (law:∀U,F U=(P).eval U • actualTransport R.family (N:=N) (fun T=>∏a∈s.val,(χ a:ℂ)⁻¹*originalSource a T) ((fk).trans live) U)
    (φ:Fin 3→X f→ℂ)(soft:Integrable (fun U=>((P).eval U:ℂ)*∏a∈s.val,φ a U) (prior G _)){u:ℕ}(uf:u≤f)(W:Config G (R.family.side u p)):
    let full:=actualTransport R.family (N:=N) (face originalSource s) ((fk).trans live)
    let paid:=fun U=>∏a∈s.val,(χ a:ℂ)*φ a U
    actualTransport R.family (N:=N) (fun U=>full U-paid U) uf W=
      amount χ s*(readingAt R (N:=N) F uf W-
        readingAt R (N:=N) (fun U=>((P).eval U:ℂ)*∏a∈s.val,φ a U) uf W):=by
  intro full paid
  let C:=amount χ s
  let cheap:=fun U=>((P).eval U:ℂ)*∏a∈s.val,φ a U
  have a₁: (fun U=>(P).eval U • full U)=C • F:=by
    funext U
    exact (Complex.real_smul ..).trans (field R d live Y o χ positive s F law U)
  have a₂: (fun U=>(P).eval U • paid U)=C • cheap:=by
    funext U
    simp only [paid,C,amount,Finset.prod_mul_distrib,cheap,Complex.real_smul,Pi.smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,M,bound⟩:=salary originalSource (old_paid R d live Y o) s
  have b₁:Integrable (fun U=>(P).eval U • full U) (prior G _):=
    actualTransport_weighted_integrable R.family R.makes (le_refl N) m.aestronglyMeasurable bound ((fk).trans live)
  have nz:C≠0:=Finset.prod_ne_zero_iff.mpr (fun a _=>Complex.ofReal_ne_zero.mpr (positive a).ne')
  have hF:Integrable F (prior G _):=by
    rw [a₁] at b₁
    have drop:=b₁.smul C⁻¹
    simpa only [smul_smul,inv_mul_cancel₀ nz,one_smul] using drop
  have b₂:Integrable (fun U=>(P).eval U • paid U) (prior G _):=a₂.symm ▸ soft.smul C
  have diff:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((fk).trans live) b₁ b₂ uf) W
  calc
    _=actualTransport R.family (N:=N) full uf W-actualTransport R.family (N:=N) paid uf W:=diff
    _=readingAt R (N:=N) (C • F) uf W-readingAt R (N:=N) (C • cheap) uf W:=by
      unfold actualTransport readingAt
      rw [a₁,a₂]
      simp only [Complex.real_smul,Complex.ofReal_inv]
    _=_:=by rw [read_scale R uf C F hF W,read_scale R uf C cheap soft W,mul_sub]


end YM.Integration.WilsonOriginalMicroscopicEntranceHeldCharge
end
