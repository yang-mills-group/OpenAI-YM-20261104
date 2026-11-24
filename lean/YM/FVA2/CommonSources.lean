import YM.FVA2.Iteration
import YM.FVA2.PenHistory
/-!
# Expose the very same marked inputs in the two period choices

Includes binding of continuum-menu MS (orders/horizons unrestricted), use conversion from
 `Main.Packing` downstream. Critical: don't equate Endμ with a differently periodic Full-period
 equation.Foreground structure `TownHistory/Every`. This just verifies exactly which stencils
 enter that continuation; if needing analytical comparison with full periods, use that title
 and all prior.Joint.Bind. We compare MS throughout by the inversion route, WITH EVERY mark.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both.Passage
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.InversionTop FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking PowerSeries Finset
open Exhibit
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}{c f n:Side}(Q:Warehouse G){I:Type}[DecidableEq I]
variable (d:I→ℕ) (u:(i:I)→Q.Atom ( d i ))(s:Finset I) (p:I→Site n)

local notation "Tκ"=> Track.Seals Q p d u
local notation "Sκ"=> Stamp.shafts Tκ s
-- full (independent) physical inputs, include off-shell real Laurent powers before comparing
-- exponent.Pow.B in solution. `Σ-degrees` applied before rotation/conversion.Dimension.

def businesses (i:I) : Ticket (Pins G n):= drop ((Tκ i).slots) (rise ( ( Tκ i ).stencil ∘ expLinks G (Edge (Site n)) ))
lemma starting (i:I) : ContDiffAt ℝ ω ( ( Tκ i ).stencil ∘ expLinks G (Edge (Site n)) ) 0:= Source.pos_jet (Q.poised _ ( u i )) _
lemma born (i:I) : X^( ( Tκ i ).slots ) * businesses Q d u p i= rise ( ( Tκ i ).stencil ∘ expLinks G (Edge (Site n)) ) := by
    unfold businesses; apply Stack.recover; intro j hj; rw [rise,coeff_mk]; apply Subtype.ext; change jet _ j=0; exact Source.below (Q.poised _ (u i)) (p i) (Q.awake _ (u i)).low j hj
lemma full_projection (i:I): boost (Trans.coverL G n) ( businesses Q d u p i )= Shipment.burn ((Tκ i).slots) ( Tκ i |>.stencil ) := by
    let X' : Ticket (Pins G n):= businesses Q d u p i; let s0:= ( Tκ i ).slots; let Y':= Shipment.burn s0 (Tκ i|>.stencil); apply PowerSeries.X_pow_mul_injective (k:=s0);
    change X^ ((Tκ i).slots) * boost (Trans.coverL G n) ( businesses Q d u p i )= X^( (Tκ i).slots )* Shipment.burn _ _; rw [ Shipment.sealBurnM, ← Shipment.boost_X,born,FormalOPE.RG10.MarkovChain.Vault.climbing _ ((starting Q d u p i).of_le le_top) ]; unfold imprintRoot imbed; apply congr_arg Stack.rise; funext x; exact congrArg ( Tκ i|>.stencil ) (Trans.assemble_exp G n x).symm

def seats (p:I→Site n) : Ticket (Pins G n):= ∏ i∈s,businesses Q d u p i
lemma arms : Shipment.UpM Q d p u s= boost (Trans.coverL G n) ( Passage.seats Q d u s p ):= by unfold seats; rw [ map_prod ]; simp_rw [ full_projection ]; rfl
lemma scripture : X^(Stamp.degrees Tκ s) * Passage.seats Q d u s p= exPay Sκ := by
    unfold Stamp.degrees seats; rw [ ← prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib ]; simp_rw [born]; unfold Stamp.shafts; rw [exPay,show (( ∏ i∈s,( Tκ i ).stencil ) ∘ _) =∏ i∈s, ( Tκ i ).stencil ∘ expLinks G (Edge (Site n)) from (?_), ExactTower.rising s (fun i _=>(starting Q d u p i).of_le le_top ) ]; funext y; simp [ Finset.prod_apply ]
variable {L:Fabric G n}(X':Exhibit L)
-- pack reports.Surface.Frame.Asset.
local notation "Mx"=> X'.prescription
open Shipment
/-- Upper root plus retained terminal choices instantiate `Up`. -/
theorem pulse_s : purchase ( Mx ).goods ( Mx ).z ( Mx ).entitled ( Mx ).calibrated ( boost (Trans.coverL G n) ( seats Q d u s p ))= Channel.realRead Tκ s := by
   rw [← Passage.arms Q d u s p]; exact Shipment.manifestedM (h0:=(Mx).pure) .. -- args

section tags
variable {B: MS.Local.Physical.Deck G} {W:Type}[LinearOrder W](d:W→ℕ)(v:W→Lattice.Cover)(U:Lattice.Cover)(s:Finset W)
    (Λ:(i:W)→ MS.Menus.Acts B (d i))(t: MS.Book.Program.Team)(x:ℝ)
local notation "Σκ"=> Track.Crew Q B d s
local notation "δ0"=> Channel.coord n U v
abbrev registers (a: Track.Crew Q B d s) : Ticket (Pins G n):= Passage.seats Q (fun i:↥s=>(a i).1.size) (fun i=>(a i).2) Finset.univ (δ0 ∘ Subtype.val)

def tagPrice (Q:Warehouse G)(U:Lattice.Cover): PowerSeries ℝ:= ∑ a: Track.Crew Q B d s, Track.debt Q d Λ x s a * Clock.reprℝ t x ( purchase ( Mx ).goods ( Mx ).z ( Mx ).entitled ( Mx ).calibrated ( boost (Trans.coverL G n) (registers (n:=n) Q d v U s a) ) )
lemma stampV (A: MS.Book.Convolve.T ℂ) : MS.Fleet.PhysicalSum G t x n true s v U (Track.request Q d Λ t) A ↔ Score.netE (tagPrice X' d v s Λ t x Q U)=A:= by
   rw [ IteratedWilsonPrescription.real_folioM ( Mx ) ]; unfold tagPrice IteratedWilsonPrescription.billM; simp_rw [Passage.arms]
end tags

end YM.FVA2.Both.Passage
