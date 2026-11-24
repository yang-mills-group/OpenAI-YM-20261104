import YM.Integration.WilsonPublicForkFiniteFaces
import YM.Integration.WilsonPublicForkIndependentFee

/-! The full physical MS detector can receive ordinary signed rows and
two-point signed rows separately. The independent finite decoder residual
and its actual normalized finite-order coefficient are common to all rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkReadings
open Next.Rank RG12 SharpGram Extraction
open Function Finset Filter Set MeasureTheory Table Spec RG17 Maxwell Climb
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater WilsonMSDictionaryVector WilsonPublicOutputRegulators
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S)(L:Layout F){I:Type}[Fintype I](X:I → External R.family S)
  {n:ℕ}(d:Fin n → ℕ)(h:ℕ)(v:∀i,Free R.family (d i))(ψ:Test n)
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
  (q:ℕ)(ins:∀i,R.family.label (d i))(out:Dframe.Toon G h → R.family.label h)(r:ℝ)

/-- The inverse cutoff stays separate from the ordered physical course. -/
theorem ordered (e:ℝ → RG17.Free R.family h) {fee:ℝ} (fp:0≤fee)
    (priced:∀ᶠ s:ℝ in atTop,WilsonPublicForkIndependentFee.dose R.family h (e s)≤fee):
    ∀(a b c η:ℝ),0≤a → 0≤b → 0≤c → 0≤η →
    ∀(ordinary:ℝ → UVIndex → I → ℂ)(gram:ℝ → UVIndex → Dframe.Toon G h → I → ℂ),
    (∃ᶠ s:ℝ in atTop,f.late fun N per=>
      (∀j,‖packMark L (X j) d ins r ψ (N,per)-ordinary s (N,per) j‖≤a*η) ∧
      (∀k j,‖headMark L (X j) h r (N,per) (out k)-gram s (N,per) k j‖≤b*η) ∧
      ∀j,‖ordinary s (N,per) j-∑k,(WilsonMSDictionaryVector.basis R.family h).repr (e s) k*gram s (N,per) k j‖≤c*η) →
    ∃ᶠ s:ℝ in atTop,f.late fun N per=>‖contrast F L X d ins out r ψ (e s) (N,per)‖≤(a+c+fee*b)*η:=by
  intro a b c η ap bp cp ep ordinary gram bills
  apply (priced.and_frequently bills).mono
  rintro s ⟨wallet,signed⟩
  apply (f.fused (fun i=>‖contrast F L X d ins out r ψ (e s) i‖≤(a+c+fee*b)*η)).mp
  have coissued:= (f.fused (fun i=>
    (∀j,‖packMark L (X j) d ins r ψ i-ordinary s i j‖≤a*η) ∧
    (∀k j,‖headMark L (X j) h r i (out k)-gram s i k j‖≤b*η) ∧
    ∀j,‖ordinary s i j-∑k,(WilsonMSDictionaryVector.basis R.family h).repr (e s) k*gram s i k j‖≤c*η)).mpr signed
  filter_upwards [coissued] with i item
  obtain ⟨prod,cols,indept⟩:=item
  exact (WilsonPublicForkFiniteFaces.measured F L X d ins out r ψ i (e s) (ordinary s i) (gram s i)
    fp (mul_nonneg ap ep) (mul_nonneg bp ep) (mul_nonneg cp ep) wallet prod cols indept).trans_eq (by ring)

theorem original :
    let P:=((ms.separatedOPE ν).wilson.light h).choose
    ∃fee:ℝ,0≤fee ∧ ∀t∈Set.Icc (-1:ℝ) 1,
    let e:=experiment R.family d h Z M ν v ψ P q t
    ∀(a b c η:ℝ),0≤a → 0≤b → 0≤c → 0≤η →
    ∀(ordinary:ℝ → UVIndex → I → ℂ)(gram:ℝ → UVIndex → Dframe.Toon G h → I → ℂ),
    (∃ᶠ s:ℝ in atTop,f.late fun N per=>
      (∀j,‖packMark L (X j) d ins r ψ (N,per)-ordinary s (N,per) j‖≤a*η) ∧
      (∀k j,‖headMark L (X j) h r (N,per) (out k)-gram s (N,per) k j‖≤b*η) ∧
      ∀j,‖ordinary s (N,per) j-∑k,(WilsonMSDictionaryVector.basis R.family h).repr (e s) k*gram s (N,per) k j‖≤c*η) →
    ∃ᶠ s:ℝ in atTop,f.late fun N per=>‖contrast F L X d ins out r ψ (e s) (N,per)‖≤(a+c+fee*b)*η:=by
  dsimp only
  obtain ⟨fee,fp,priced⟩:=WilsonPublicForkIndependentFee.original R.family d h Z M ν v ψ ms q
  refine ⟨fee,fp,?_⟩
  intro t ht a b c η ap bp cp ep ordinary gram bills
  let P:=((ms.separatedOPE ν).wilson.light h).choose
  let e:=experiment R.family d h Z M ν v ψ P q t
  exact ordered F L X d h ψ ins out r e fp (priced t ht) a b c η ap bp cp ep ordinary gram bills

end YM.Integration.WilsonPublicForkReadings
