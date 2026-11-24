import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Unique
import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Wire
/-! # (G9) The field-domain derivative ACTUALLY differentiates the formal series.
    On Y and on the independent V kernels, at full-layout coordinates in any fixed cap;
    all shape derivatives thus exact. Use to increase precision before moving y. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Read Comparing Pose Original Matrix Quotes
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion))
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    (h : Shop U J N) (hp: normal U J N.store)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "μ" => (physicalY U Y none)
variable (Q:Spare N (d+1)) (a:Axis) (v:Tags G d n)(j:Fin n) {x:Points n} (hx:x∈conf n)
local notation "T" => Toon G (d+1)
abbrev offered (v:Tags G d n)(j:Fin n)(c:Sec G (d+1)) := update (up (Nat.le_succ _) ∘ v) j c
abbrev roster (v:Tags G d n)(j:Fin n)(b: Toon G (d+1)) := offered v j (theory b)
local notation "dₘ" => Points.gradient j a
def flare (x:Points n) : PowerSeries ℂ := ∑ i:T,sizeIt N Q (v j) a i * storyV N (roster v j i) x
include hx
lemma directional {r:ℝ}(w:Viewers U)(hr:0<r)(hv : heights U Y r (d+1)) :
    Points.gradient j a (physicalY U Y w v r) x =
      ∑ b:T, coord b (upgrade U Y d r a (v j)) * physicalY U Y w (roster v j b) r x := by
  refine Eq.trans (column U Y w hr hx hv v a j) ?_
  let L:= (trueK U Y w r x (d+1)).toLinearMap (up (Nat.le_succ _) ∘ v) j; let F:= upgrade U Y d r a (v j)
  change L F = _; rw [beats]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
omit hx
include H
lemma growing (k:ℕ) : ContDiffOn ℝ ∞ (fun x=> coeff k (flare N Q a v j x)) (conf n) := by
   simp_rw [ flare,map_sum,coeff_mul ]; exact ContDiffOn.sum fun b _=> ContDiffOn.sum fun p _=> contDiffOn_const.mul (PT_cost N M H _ _)
include hJ h hp P
variable {r:I→ℝ} (hr:Tendsto r L late) {y:I→Points n} {K:Set (Points n)} (hc:IsCompact K)(hz:K⊆conf n)(hy:∀ᶠ i in L,y i∈K)
include hr hc hz hy in
lemma fiery (p:ℕ) :
    Coin L Pose.home (t ∘ r) (δ ∘ r) p Pose.home (fun i=> dₘ (μ v (r i)) (y i)) (fun i=> flare N Q a v j (y i)) := by
  let τ:=t∘r; let g:= δ∘r; have hf := Pose.guaranteed U J hJ N hp M H h
  let h0:= one_paid L; let p0 := sizeIt N Q (v j) a; let X (b:Toon G (d+1)) i := coord b (upgrade U Y d (r i) a (v j))
  have he b: Coin L Pose.home τ g p Pose.home (fun i=> X b i * μ (roster v j b) (r i) (y i)) (fun i=>p0 b * storyV N (roster v j b) (y i)) := by
     let h:= Coin.mul (peson _ _ _ _ H P hf hr) (hr.eventually ((coupling_payment sim hf).mono fun i hi=> hi.2.1)) (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) h0 (Worth.comp hr (size U J Y N hJ P M H h hp Q (v j) a b) p) (point_coin U J Y N hJ P M H h hp (roster v j b) K y hr hc hz hy p)
     exact h.congr (EventuallyEq.refl ..) (EventuallyEq.refl ..) (Eventually.of_forall fun _=> one_mul _)
  refine (Coin.sum h0 (s:= Finset.univ) (fun b _=>he b)).congr ?_ (EventuallyEq.refl ..) (EventuallyEq.refl ..)
  filter_upwards [hr.eventually (height (taking U J Y N hJ P M H h hp) (d+1)),hr.eventually self_mem_nhdsWithin,hy] with i hi e w
  exact (directional U Y a v j (hz w) _ e hi).symm
variable (p:Test n)
lemma jet_read (k:ℕ) : (Coin late Pose.home t δ k Pose.home (fun i=>p.applyTo (dₘ (μ v i))) (fun _=>profile (flare N Q a v j) p)) := by
  refine test_coin p (fun k=>(growing N M H Q a v j k).continuousOn) _ _ _ _ ?_ (fiery U J Y N hJ P M H h hp Q a v j (K:=tsupport p) tendsto_fst p.hasCompactSupport p.tsupport_subset placed k)
  filter_upwards [self_mem_nhdsWithin] with i hi; exact (dcost (fun x hx=>(regular_at U Y _ hi hx v).contDiffWithinAt) j a).continuousOn
lemma learned : profile (flare N Q a v j) p=profile (storyV N v) (shiftT j a p) := by
  let F:= Pose.guaranteed U J hJ N hp M H h
  apply Worth.unique (jet_read U J Y N hJ P M H h hp Q a v j p) _ (clock_scale sim F) (heading J Y t M H P F (r:=id) (by exact tendsto_id))
  intro k; refine (true_coin U J Y N hJ P M H h hp (shiftT j a p) v k).congr ?_ (EventuallyEq.refl ..) (EventuallyEq.refl ..); filter_upwards [self_mem_nhdsWithin] with i hi
  exact Eq.symm ( Sparks.translate p _ (fun x hx=>(regular_at U Y _ hi hx v).contDiffWithinAt ) j a )
include hx
lemma derivative_eq (k:ℕ) : Points.gradient j a (fun x=>coeff k (storyV N v x)) x = coeff k (flare N Q a v j x) := by
  refine Test.unique_kernel ?_ (growing N M H Q a v j k).continuousOn |>.1 ?_ hx
  · exact (dcost (PT_cost N M H v k) j a).continuousOn
  intro p; have hh:=congr_arg (coeff k) (learned U J Y N hJ P M H h hp Q a v j p); rw [ Sparks.profile,Sparks.profile,coeff_mk,coeff_mk ] at hh; exact ( Sparks.translate p _ (PT_cost N M H v k) j a).trans hh.symm
end YM.FVA2.GradedFar259.Sparks
