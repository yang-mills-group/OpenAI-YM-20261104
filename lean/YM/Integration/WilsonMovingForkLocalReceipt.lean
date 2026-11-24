import YM.Integration.WilsonMovingForkSharedStop
import YM.Integration.WilsonMovingForkProbeWindow

/-! From actually filed compact and original positions directly to their true public scalar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkLocalReceipt
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedBranchStencil
open OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonReflectedPublicStationFare (station)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMovingForkHeterogeneousCut (Filed Heard Invoice)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][DecidableEq I][Nonempty I]

open WilsonMovingForkProbeEars (Charge)
open WilsonMovingForkPointHousing (Fits)

variable {D T B n u:ℕ}(d:I→Fin (D+1))(x:∀i,Free R.family (d i).val){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (η M:ℝ)(r:ℝ)(ρ:I→{s:ℝ //0<s ∧ s<δ})(look:Fin n ↪ I)

def physical (i:Fin n):S.Tag:=
  ⟨(d (look i)).val,homogeneous F J Z (ρ (look i)).val (d (look i)).val (x (look i))⟩

/-- One file and both earlier scalar dates are chosen before the positions.
The same angular inverse is used by the full genuine Duhamel return. -/
structure Submitted (pred:Points n→ℂ) where
  weak:Fin n→Bool
  K:ℕ
  reporter_le:reporter F books ρ ≤ K
  file:Filed R (fun i=>(d (look i)).val) K
  names:∀i,file.station i=station F ((books (ρ (look i))).rows (d (look i))) (weak i)
  v:ℕ
  c:ℕ
  fixed:u≤v
  older:v≤c
  before:c≤K
  invoice:Invoice
  positive:0≤ invoice.total v c K
  joint:∀o:Fin n → Cover,
    (∀i,‖R.family.S.gridPoint (reporter F books ρ) (o i)‖≤(M+1)*outer z B r) →
    (Pairwise fun i k=>(η/2)*r≤‖R.family.S.gridPoint (reporter F books ρ) (o i)-R.family.S.gridPoint (reporter F books ρ) (o k)‖) →
    Heard (f:=f) file fixed older before reporter_le
      (fun i=>((books (ρ (look i))).rows (d (look i))).arm (weak i) (physical F J Z d x ρ look i).2) o pred invoice

omit [DecidableEq I] [Nonempty I] in
theorem original (P q:ℕ)(E:Type)[Fintype E](sale:Charge F J Z D T B d x books η M u P q n look E):
    ∃m:ℕ,∃C₀ D₀:ℝ,0≤C₀ ∧ 0<D₀ ∧ ∀ᶠr in trail,∀rp:0<r,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃i,(ρ i).val=r) →
      ∀pred:Points n→ℂ,∀A:Submitted F J Z (B:=B) (u:=u) d x books η M r ρ look pred,
      ∀ref:E → E4,∀y:Points n,Fits r (outer z B r) M η y →
      let j:=reporter F books ρ
      let X:=r⁻¹ • y
      let prog:=sold m ref (div_pos (R.family.S.a_pos j) rp) X
      let values:=fun Y:Points n=>pred (r • Y)
      ‖S.useAt S y (physical F J Z d x ρ look)-pred y‖≤C₀*(∏i:Fin n,‖x (look i)‖)*(wilson z r)^P +
        (total n m E)^levels n*(D₀*(wilson z r)^q+A.invoice.total A.v A.c A.K)+‖read prog values-values X‖:=by
  obtain ⟨m,C₀,D₀,cn,dn,all⟩:=sale
  refine ⟨m,C₀,D₀,cn,dn,?_⟩
  filter_upwards [all] with r room
  intro rp ρ band near pred A ref y fits j X prog values
  obtain ⟨_,rows⟩:=room rp ρ band near
  have head:=rows A.weak A.K A.reporter_le A.file A.names A.v A.c A.fixed A.older A.before pred A.invoice A.positive
    (fun o held=>A.joint o held.1 held.2) ref X fits.1 fits.2
  have eq:r • X=y:=smul_inv_smul₀ rp.ne' _
  have tested:=head.2
  rw [eq] at tested
  exact tested

end YM.Integration.WilsonMovingForkLocalReceipt
