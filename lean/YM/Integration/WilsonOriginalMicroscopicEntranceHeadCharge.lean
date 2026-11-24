import YM.Integration.WilsonOriginalMicroscopicEntranceGridStock
import YM.Integration.WilsonOriginalMicroscopicEntranceSockets
import YM.Integration.WilsonThermometerUnitFilingCoarse

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeadCharge
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
open WilsonThermometerUnitFilingCoarse (reading)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (d:Fin 3→ℕ) {N p f n:ℕ} (live:f+n≤N)
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)
local notation "fk" => Nat.le_add_right f n
local notation "P" => R.family.path.rep N p f
variable (Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
local notation "originalSource" => old R d ((fk).trans live) Y o

def amount (χ:Fin 3→ℝ) (s:(J).Mode):ℂ:=∏a∈s.val,(χ a:ℂ)

theorem field (χ:Fin 3→ℝ) (positive:∀a,0<χ a)(s:(J).Mode)(F:X f→ℂ)
    (law:∀U,F U=(P).eval U • actualTransport R.family (N:=N) (fun T=>∏a∈s.val,(χ a:ℂ)⁻¹*originalSource a T) ((fk).trans live) U)(U:X f):
      ((P).eval U:ℂ)*actualTransport R.family (N:=N) (face originalSource s) ((fk).trans live) U=amount χ s*F U:=by
  have nz:amount χ s≠0:=Finset.prod_ne_zero_iff.mpr (fun a _=>Complex.ofReal_ne_zero.mpr (positive a).ne')
  have reshape:(fun T=>∏a∈s.val,(χ a:ℂ)⁻¹*originalSource a T)=fun T=>(amount χ s)⁻¹*face originalSource s T:=by
    funext T
    simp only [amount,face,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  rw [law,reshape,WilsonOriginalMicroscopicEntranceSockets.scaled R (le_refl _) ((fk).trans live)
    (face originalSource s) (salary originalSource (old_paid R d live Y o) s) (amount χ s)⁻¹ U,Complex.real_smul]
  field_simp [nz]

private theorem read_scale {j:ℕ} (jf:j≤f)(c:ℂ)(F:X f→ℂ)(hf:Integrable F (prior G _)):
    reading R (N:=N) (c • F) j jf=c*reading R (N:=N) F j jf:=by
  unfold reading
  rw [scale R c F hf jf]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem original (χ:Fin 3→ℝ)(positive:∀a,0<χ a)(s:(J).Mode)(F:X f→ℂ)
    (law:∀U,F U=(P).eval U • actualTransport R.family (N:=N) (fun T=>∏a∈s.val,(χ a:ℂ)⁻¹*originalSource a T) ((fk).trans live) U)
    (φ:Fin 3→X f→ℂ)(soft:Integrable (fun U=>((P).eval U:ℂ)*∏a∈s.val,φ a U) (prior G _)){u:ℕ}(uf:u≤f):
    let full:=actualTransport R.family (N:=N) (face originalSource s) ((fk).trans live)
    let paid:=fun U=>∏a∈s.val,(χ a:ℂ)*φ a U
    actualTransport R.family (N:=N) (fun U=>full U-paid U) uf 1=
      amount χ s*(reading R (N:=N) F u uf-
        reading R (N:=N) (fun U=>((P).eval U:ℂ)*∏a∈s.val,φ a U) u uf):=by
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
  have diff:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((fk).trans live) b₁ b₂ uf) 1
  calc
    _=actualTransport R.family (N:=N) full uf 1-actualTransport R.family (N:=N) paid uf 1:=diff
    _=reading R (N:=N) (C • F) u uf-reading R (N:=N) (C • cheap) u uf:=by
      unfold actualTransport reading
      rw [a₁,a₂]
      simp only [Complex.real_smul,Complex.ofReal_inv]
    _=_:=by rw [read_scale R uf C F hF,read_scale R uf C cheap soft,mul_sub]


end YM.Integration.WilsonOriginalMicroscopicEntranceHeadCharge
end
