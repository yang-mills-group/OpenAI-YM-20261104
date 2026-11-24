import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Knobs
/-! # Transfer to operator cost for ALL real viewers & all inputs
    (complex basis norm on Sec). `indexed`: first leg argument in list is first direction
    taken, always costs for r units. Empty list recovers actual moment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ}{I:Type}{F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {K:Set (Points n)}{E:Set (Points m)}{x:I→Points n}{y:I→Points m}{r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S)(N:WilsonPrescription G)(Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(H0:LogTrace U Q.port)
    (hJ : Leading U J)(hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial){A' :∀ d:ℕ,ℝ→Change G d}
    (P:Realized J Y N A' (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "g" => (fun i=>g0 G (r i))
local notation "t" => Paper.meter U J N.criterion
local notation "τ" => t ∘ r
local notation "Φ" => (fun i=>joins (x i) (y i) (T i))
-- purely multilinearity at derivative level
section linear
variable {f: Points m→ Structure1.Point G d m} (he:∀ u:Tags G d m,ContDiffOn ℝ ∞ (fun x=> f x u) (conf m))
  (u:Tags G d m) {x:Points m} (hx:x∈conf m)(q: List (Fin m × Axis))
include hx
include he
lemma any_labels : dots q (fun x=> f x u) x=∑ b: BasisSlots G (fun _:Fin m=>d), coordinates b u*dots q (fun x=>f x (word b)) x := by
  simp_rw [word_sigma u,smul_eq_mul]
  rw [dsums q hx Finset.univ _ (fun j _=> contDiffOn_const.mul (he _))]; exact Finset.sum_congr rfl fun _ _=> dconst q hx (he _) _
omit he
include H
lemma book_entry : indexed N q u x=∑ b: BasisSlots G (fun _:Fin m=>d), PowerSeries.C (coordinates b u)*indexed N q (word b) x := by
  ext1 i; simp_rw [map_sum,coeff_C_mul, Sparks.indexed, coeff_mk];
  apply any_labels (f:=fun x=> fxt (V d) x i) _ u hx q
  intro v; simpa only [story_charge] using (PT_cost N M H v i)
lemma paid_top (p:ℕ) (s:ℝ) : dots q (fun x=>crop p s (storyV N u x)) x=crop p s (indexed N q u x) := by
  simp_rw [crop_apply]; rw [dsums q hx _ _ (fun i _=> contDiffOn_const.mul (PT_cost N M H u _))]; exact Finset.sum_congr rfl (fun i _=>by
    rw [dconst q hx (PT_cost N M H u _)]; apply congr_arg; exact Eq.symm ( coeff_mk .. ))
end linear
variable (h : Aim F G W a b r T) (R:Room W c δ A B)(hx:∀ᶠ i in F,x i∈K)(hy:∀ᶠ i in F,y i∈E)(hm:Amplifies K A)(hv: Amplifies E B)
    (o:I→Viewers U) (L : Loader G U J N W K E)
    (ha:0<a)(hb:0<b) (ν:ℝ) (l : List (Fin (n+m)×Axis))
variable (v : I→ Tags G d (n+m))(u : ℝ) (hu:0≤u)(hw:∀ᶠ i in F,v i ∈ Balls u G (fun _=>d))
include P hJ U J Y N M H Q H0 S0 S1 hp hx hy R h hm hv ha hb ν L hw hu
lemma enlarging (p:ℕ) : Coin F T τ g p Pose.home
    (fun i=> dots l (physicalY U Y (o i) (v i) (r i)) (Φ i)) (fun i=> indexed N l (v i) (Φ i)) := by
  let Y' i:= dots l (physicalY U Y (o i) (v i) (r i)) (Φ i)
  have Vh b:= fitted U J Y N Q H0 hJ hp M H P S0 S1 h R hx hy hm hv (word b) o L ha hb ν l p (d:=d)
  have hT := aspirant R h; have he:= Pose.guaranteed U J hJ N hp M H S1
  have e (j: BasisSlots G (fun _:Fin (n+m)=>d)) := Coin.mul (peson _ _ _ _ H P he h.reach) (h.reach.eventually ((coupling_payment sim he).mono fun i hi=>hi.2.1))
    (h.reach.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) hT (Coin.literal _ (Fare.cent (hw.mono fun i hi=>coord_price hu (v i) hi j))) (Vh j)
  have hk := permit R h (hx.mono fun i hi=> includes hm hi) (hy.mono fun i hi=> includes hv hi)
  refine ( Coin.sum hT (s:=Finset.univ) (fun j _=> e j) ).congr ?_ ?_ (Eventually.of_forall fun _=>one_mul _)
  · filter_upwards [h.reach.eventually self_mem_nhdsWithin,hk] with i hi hx
    exact (any_labels (fun u:Tags G d (n+m)=> fun x (hx:x∈conf _)=> (regular_at U Y (o i) hi hx u).contDiffWithinAt) (v i) hx l).symm
  filter_upwards [hk] with i hi; exact (book_entry N M H (v i) hi l).symm
end YM.FVA2.GradedFar259.Flash
