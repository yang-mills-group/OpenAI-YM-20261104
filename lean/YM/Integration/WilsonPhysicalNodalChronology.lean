import YM.Integration.WilsonPhysicalOrdinaryPinExpense
import YM.Integration.WilsonMovingForkChronologicalSale

/-! The independent residual in a physical pin is the sum of the issued
chronological differences on the two original flat receivers. Its far
terminal is the actual filed finite Wilson figure on the named sample. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalChronology
open Filter Set Function Finset Lattice Wilson RG Source Labels MeasureTheory PhysicalNext.Repeat.Legato
open Pert.Asymptotics RegulatorIR.FVAAlt2 XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open Extraction Table Spec OPE OPE.Orbits Climb Trace.Pilot Next.UVStress PhysMS Maxwell
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkPrintedFile (Program row allSlots)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(d:Fin n→ℕ)
    {N per site K c u v:ℕ}(file:Filed R d K)(Y:∀i,R.family.label (d i))
    (prog:Program R d K)(addr:Fin n→ Cover)(node:Sample n)
    (sk:site≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)(kn:K≤N)
local notation "pin" => seats (R:=R) sk per addr
local notation "w" => doses R d file.station (N:=N) (per:=per) (file.A N per) Y
local notation "M" => row prog N per w pin
local notation "Φ" i:max => numerator R N per i (M i)
local notation "Rdg" i:max j:max live:max => reading R (N:=N) (Φ i) j live
local notation "heat" => regulatorRun R.family N per K
local notation "B₀" => board R W d (vector R d (N:=N) (per:=per) file Y) node univ
local notation "ξ₀" => signed R W d (N:=N) (per:=per) file Y (uv.trans (vc.trans ck)) node
local notation "px" => ∀i,wrap (R.family.side K per) (node.layout i)=pin i
local notation "wt" => (∀ i : ℕ, v ≤ i → i ≤ K → Mounted prog N per w pin i)

include kn

/-- The full occupied face of the chronological row is integrable under the
earlier Wilson prior from its actual mounted salaries at that date. -/
private theorem charged {i:ℕ}(ik:i≤K)(live:Mounted prog N per w pin i):
    Integrable (Φ i) (prior G _):=
  (WilsonMovingForkChronologicalTable.full prog N per w pin i) ▸
    (Marker.Poly.get (allSlots n)).integrable_comp (WilsonMovingForkChronologicalSale.integrable prog N per w pin ik kn live)

theorem signed_table (placed:px)(issued:wt)(q:ℕ):
    ξ₀ q=(∑j∈Ico c K,feeAt R N per u M j)+(Rdg c u (uv.trans vc)-Rdg c v vc)+
      (∑j∈Ico v c,feeAt R N per v M j)+(Rdg v v le_rfl-evaluated q heat B₀):=by
  have reached:=WilsonOriginalPublicNodalSeed.field R W d (N:=N) (per:=per) file Y sk kn (uv.trans (vc.trans ck)) addr node placed q
  have exactTop:M K=product R d (N:=N) pin w:=by
    funext U
    simp [WilsonMovingForkPrintedFile.row]
  have atK:Rdg K u (uv.trans (vc.trans ck))=actualTransport R.family
      (N:=N) (p:=per) (product R d (N:=N) pin w) (uv.trans (vc.trans ck)) 1:=by
    rw [exactTop]
    exact WilsonThermometerUnitFilingPosterior.weighted R _ _
  have fine:=WilsonOriginalTwoFlatTelescope.interval R (uv.trans vc) ck kn M
    (fun j cj jk=>charged R d file Y prog addr sk kn jk (issued _ (vc.trans cj) jk))
  have coarse:=WilsonOriginalTwoFlatTelescope.interval R (le_refl v) vc (ck.trans kn) M
    (fun j vj jc=>charged R d file Y prog addr sk kn (jc.trans ck) (issued _ vj (jc.trans ck)))
  rw [←atK] at reached
  rw [←reached,←fine,←coarse]
  abel

theorem expenses (placed:px)(issued:wt)(q:ℕ)(upper lower:ℕ→ℝ)(shift terminal:ℝ)
    (old:∀j∈Finset.Ico c K,‖feeAt R N per u M j‖ ≤ upper j)
    (captured:‖Rdg c u (uv.trans vc)-Rdg c v vc‖ ≤ shift)
    (late:∀j∈Finset.Ico v c,‖feeAt R N per v M j‖ ≤ lower j)
    (bottom:‖Rdg v v le_rfl-evaluated q heat B₀‖≤terminal):
    ‖ξ₀ q‖≤(∑j∈Ico c K,upper j)+shift+(∑j∈Ico v c,lower j)+terminal:=by
  rw [signed_table R W d file Y prog addr node sk uv vc ck kn placed issued q]
  calc
    _≤((‖∑ j∈Ico c K,feeAt R N per u M j‖+‖Rdg c u (uv.trans vc)-Rdg c v vc‖)+
        ‖∑ j∈Ico v c,feeAt R N per v M j‖)+‖Rdg v v le_rfl-evaluated q heat B₀‖:=
      (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)) le_rfl)
    _≤_:=add_le_add (add_le_add (add_le_add ((norm_sum_le ..).trans (sum_le_sum old)) captured)
      ((norm_sum_le ..).trans (sum_le_sum late))) bottom

end YM.Integration.WilsonPhysicalNodalChronology
end

