import YM.FVA2.Hearth.Route
/-!
 # Track the terminal common vacuum scalar, not a scalar on every step

 Allow prefix stitched onto any other physical hierarchy. The open state share then
 factors the terminal tree. No sharing of tree links with subsequent ground levels. Supplies map-valued compatibility; stronger orders needed ONLY when
 undoing negative Laurent powers at final or when using analytic estimates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side}{L:Fabric G n} {J:ChartRatio G}

lemma wallE {n:Side}(L: Fabric G n):Even (Bottom L).val:= by
 cases L with
 | endcap k h=> exact h
 | layer _ _ _ _ L=> exact wallE L
termination_by structural L
def dropWall {n:Side}{L:Fabric G n}(T:Cloth L) : (Fabric.endcap (G:=G) (Bottom L) (wallE L)).loom.Truss:= by
 cases T with
 | floor k h T=> exact T
 | @inLayer c f S h t hf L P C=> exact dropWall (L:=L) C
termination_by structural T
 def finish (T:Cloth L) : Cloth (endcap (G:=G) (Bottom L) (wallE L)):= Cloth.floor _ (wallE L) (dropWall T)
-- Equations confirm open terminal AND pull into continuing arc
variable {n:Side}{L:Fabric G n}
lemma permissions {n:Side}{L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(A:Ticket (Flats G n))(h:Commission J T U z):
 (drag (castAt (finish T)) (drive T z U A J h).1.Q).RespectsPrice:= by
 cases T with
 | floor=> exact h
 | inLayer P C=> exact permissions C _ _ _ (Exists.choose_spec h)
termination_by structural T

lemma finish_line {n:Side}{L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(A:Ticket (Flats G n))(h:Commission J T U z):
 course T z U J A h= enjoy (permissions T z U A h).inner (tangent G (finish T).choose.Bulk)
 (boost (castAt (finish T)) (drive T z U A J h).2) (boost (castAt (finish T)) (drive T z U A J h).1.W*tissue J (finish T).choose.Bulk):= by
 cases T with
 | floor=> rfl
 | inLayer P C=> exact finish_line C _ _ _ (Exists.choose_spec h)
termination_by structural T

-- common vacuum extracted *after*, including Assembly schedule.
variable (T: Cloth L)(z:L.Accounts→PowerSeries ℝ)(H:∀ i,0<term (z i) 0)(HJ:LocalRatio J)
local notation "U"=> headquarters z
local notation "Ω"=> Field (Cloth.choose (finish T))
local notation "q"=> collared T z HJ H
local notation "ν"=> tangent G (Loom.Truss.Bulk (Cloth.choose (finish T)))

-- scalar λ at terminal.Frame. explicit
 def flat (A:Ticket (Flats G n)) : Ticket Ω:= boost (castAt (finish T)) (drive T (z∘some) U A J q).1.W * tissue J (finish T).choose.Bulk
 def quiet (A:Ticket (Flats G n)) : Law Ω:= (permissions T _ _ A q).inner

variable (A:Ticket (Flats G n))
lemma flat_one : flat T z H HJ 1=flat T z H HJ A:= by unfold flat; rw [any_state T T z H HJ HJ 1 A]
lemma law_one : quiet T z H HJ 1=quiet T z H HJ A:= by unfold quiet; congr 1; rw [any_state T T z H HJ HJ 1 A] -- inspect
 def vacuum : PowerSeries ℝ:= input (quiet T z H HJ 1) ν (flat T z H HJ 1)
 def current : Ticket Ω:= boost (castAt (finish T)) (drive T (z∘some) U A J q).2
 def tally : PowerSeries ℝ:= input (quiet T z H HJ 1) ν (flat T z H HJ 1*current T z H HJ A)
lemma flatful : incline (flat T z H HJ A):= by
 unfold flat; rw [←avowed T _ _ q HJ A]; exact pool (preserve_boost _ (Quadratic.upright _ _ _ (reserve _ _ _ J HJ (OpenSlots.restores ..)))) (awake HJ)
lemma vacuum_ok : constantCoeff (vacuum T z H HJ) =1:= underBudget _ _ (flatful T z H HJ 1)
theorem sold : tally T z H HJ A * (vacuum T z H HJ)⁻¹= purchase T z H HJ A := by
 unfold tally vacuum purchase; unfold current; rw [flat_one T z H HJ A, law_one T z H HJ A]; exact (finish_line T _ _ A q).symm
end YM.FVA2.Hearth
