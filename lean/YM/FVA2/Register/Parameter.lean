import YM.FVA2.Recall.Epoched
/-!
# The Epoch presentation reexpressed in the MS coupling variable

Rescalings as in `Recall`, e.g. for the unnormalized
polynomial data with an open coarse field. See `posed`,`on_clock`. This connects
also the clock datastructures to `PhysicalSum`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Register
open Function Set Filter Finset MeasureTheory Metric Lattice Wilson
open YM.FVA2 Recall Recall.Move
open MS MS.Plane MS.Koszul MS.Book MS.Book.Convolve Program MS.Native MS.Theater MS.Menus MS.Local.Physical MS.Land
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near MS.Rake Press XPos Change Slice
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking BlockGauge BlockGauge.Fabric OpenSlots.Quadratic
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Orb Facade Hearth RGComparison.Core16
open PowerSeries (coeff)
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {n:Side}
local notation "ν"=>PowerSeries.map Complex.ofRealHom

def quota (p:Team)(x:ℝ): PowerSeries ℝ:= PowerSeries.mk (fun i=> (coeff i (Program.shift p x)).re)
lemma exists_frame (p:Team)(x:ℝ): ∃ m: Move, m.frame= quota p x := from_move _ (by rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply, quota, PowerSeries.coeff_mk,share]; rfl) (by rw [quota,PowerSeries.coeff_mk,Program.ann]; rfl)
def offered (p:Team)(x:ℝ): Move:= (exists_frame p x).choose
theorem delivered (p:Team)(x:ℝ): ν (Recall.Move.frame (offered p x))=Program.shift p x := by
 rw [show Recall.Move.frame (offered p x)=_ from (exists_frame p x).choose_spec]; apply PowerSeries.ext; intro i; obtain ⟨v,hp,h⟩:= ( shiftR p i ); rw [PowerSeries.coeff_map,quota,PowerSeries.coeff_mk, show coeff i (Program.shift p x)= _ from congr_fun h x]; simp
-- position or another running variable. the same `Move` for all the steps.
variable {P:Cn} (m:Move)(h:P=PowerSeries.map Complex.ofRealHom m.frame)
include h
theorem report (T:PowerSeries ℝ): substitute P (Slice.record T)= Slice.record (m.sponsor T):= by
 funext i; simp_rw [ rules, cut,Slice.record,frame_stamp, h, ← map_pow (ν), PowerSeries.coeff_map, Complex.ofRealHom_eq_coe, YM.PertExtension.Position.AlignSeries.subst_finite m.grounded ]; rw [show Finset.Iic i= Finset.range (i+1) from Finset.ext (fun k=> by simp), Complex.ofReal_sum ]; refine sum_congr rfl (fun k _=>?_); rw [Complex.ofReal_mul,smul_eq_mul,mul_comm]
omit h

namespace Rescaled
open Arrival
variable (Y:XSpace.Initialize G) (E:Epoch G n) {J:Precision.ChartRatio G}(hj:Precision.LocalRatio J)
local notation "p"=> Epoch.T E
local notation "w"=> ( Recall.Move.weight m ∘ Gear.loops ( Epoch.clock E ))
set_option quotPrecheck false

def costo (b:List (Birth G)) : PowerSeries ℝ := Birth.scan b (fun l=> purchase E.T w (Recall.Move.still m (Gear.loops E.clock) (Gear.priced E.clock)) hj ( m.walk _ (markValue Y l n) ))
theorem exactly (b:List (Birth G)): m.sponsor (Birth.words Y n b)= costo m Y E hj b:= by
 unfold Birth.words costo; simp_rw [Recall.Move.there m Y E.clock E.T hj]; exact Birth.dist (F:=Folio.coefficients Y n) (m.sponsor.toAddMonoidHom) b -- function defeq
-- source dictionary exactly, not omitting fees.
variable {W:Type}[LinearOrder W] (u:W→ MS.Rake.Label (Press.portDeck G))(M: Land.Prescription (Press.portDeck G)) (L: Cover) (d:W→ Cover) (x:ℝ)(k:Finset W)
local notation "Γ"=> Epoch.T E
local notation "A"=> Top.value Y u M L d n x k
local notation "B"=> ApplyMF (Press.wickInput Y) ( Stripped M.team ) M u

-- representation within the shared state, on the bare variables t of an arbitrary Move. Use provided one for MS.
def posed : MS.Book.Convolve.T ℂ:= Change.convertSources (Dictionary.paid u M x) k.toList (fun l=> Slice.record ( costo m Y E hj (l.map (Top.declares u L d))))
local notation "F"=> posed (offered M.team x) Y E hj u M L d x k
omit [LinearOrder W] in
lemma top_act (h: ν (frame m)=Program.shift M.team x) : posed m Y E hj u M L d x k=A:= by
 unfold Top.value posed; simp_rw [ report m h.symm, exactly m Y E hj ]; -- hp argument order check
lemma on_clock : PhysicalSum G M.team x n true k d L ( B ) (posed (offered M.team x) Y E hj u M L d x k):= by
 rw [top_act _ Y E hj u M L d x k (delivered _ x)]; exact Top.tallies Y u M L d n x k E.F.even
end Rescaled
end YM.FVA2.Register
