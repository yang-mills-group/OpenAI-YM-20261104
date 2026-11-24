import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Invert
/-! # Register the derivative map itself. Proof with test-crossing all W/H
 assumptions as in `QScale`. No derivative price bought a priori. -/
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
local notation "c" => PowerSeries.C (R:=ℂ)

variable (Q:Spare N (d+1)) (p:Sec G d) (a:Axis)
def speeds (R:Spare N d) := R.tally.map (PowerSeries.C (R:=ℂ)) * loadMatrix N R.axis
def trueD (Q:Spare N d)(r:ℝ) : Matrix (Toon G d) (Toon G d) ℂ := Q.tally * Matrix.of (fun (i:Q.axis) j=> i.val.1.applyTo (μ (levy i.val (theory j)) r))
def circulate : Q.axis→PowerSeries ℂ := fun i=> profile (storyV N (levy i.val (up (Nat.le_succ _) p))) (shiftT 0 a i.val.1)
def earned : (Toon G (d+1))→PowerSeries ℂ := Q.tally.map (PowerSeries.C (R:=ℂ)) *ᵥ circulate N Q p a
def trueLedger (r:ℝ) := Q.tally *ᵥ fun i:Q.axis=> (shiftT 0 a i.val.1).applyTo (μ (levy i.val (up (Nat.le_succ _) p)) r)
def sizeIt : Toon G (d+1)→ PowerSeries ℂ := (speeds N Q)⁻¹ *ᵥ earned N Q p a
lemma nominal (R:Spare N d) : (speeds N R).map (constantCoeff (R:=ℂ))=1 := by
  refine Eq.trans ?_ R.invert; apply Matrix.ext; intro i j
  simp [speeds, Matrix.mul_apply]

lemma departing (b:Q.axis){r:ℝ}(hr:0<r)(hi:heights U Y r (d+1)) :
    (∑ i:Toon G (d+1), b.val.1.applyTo (μ (levy b.val (theory i)) r) * coord i (upgrade U Y d r a p))= (shiftT 0 a b.val.1).applyTo (μ (levy b.val (up (Nat.le_succ _) p)) r) := by
  let w (p:Sec G (d+1)):= levy b.val p
  let η y := μ (w (up (Nat.le_succ _) p)) r y
  let f:= b.val.1; let D(v:Sec G (d+1)) x := μ (w v) r x; let v := upgrade U Y d r a p; have he x : D v x= ∑ i, D (theory i) x * coord i v := beats ((Levy.linear₂ (trueK U Y none r x (d+1))).flip (prism (theory b.val.2))) v
  have q : ContDiffOn ℝ ∞ η (conf 2) := fun x hx=>(regular_at U Y _ hr hx _).contDiffWithinAt; rw [← translate b.val.1 _ (show ContDiffOn ℝ ∞ η (conf 2) from q)]
  have Yx x (hx:x∈conf 2): Points.gradient 0 a η x=D v x := by
    let u := w (up (Nat.le_succ _) p); have h:= entry U Y none hr hx hi (he:=(le_refl _)) u p a 0
    rw [show update u 0 (up (Nat.le_succ _) p)= u from update_eq_self 0 u] at h
    change Points.gradient 0 a (fun y=>(trueK U Y none r y (d+1)) u) x=D v x; rw [h]; change _=trueK U Y none r _ _ (w v); congr 1; funext i; fin_cases i <;> first| simp <;> rfl| rfl
  symm
  calc
     _ = f.applyTo (fun x=>∑ i, D (theory i) x * coord i v) := f.apply_eq fun x hx=> (Yx x hx).trans (he x)
     _ = _ := by unfold Test.applyTo; simp_rw [Finset.mul_sum]; rw [ integral_finsetSum ]; · exact Finset.sum_congr rfl (fun i _=> by rw [ ← integral_mul_const ]; exact integral_congr_ae (Eventually.of_forall fun x=>Eq.symm (mul_assoc ..)) )
                 intro i _; exact b.val.1.smearing (ContinuousOn.mul_const (fun x hx=> (regular_at U Y none hr hx (w (theory i))).continuousAt.continuousWithinAt) _)
include P H hJ hp h
lemma taking : Leading U Y := Realized.leading U J Y N t hJ P ((candidate_fee N t M H (Pose.guaranteed U J hJ N hp M H h)).trans_tendsto (g0_zero sim))
lemma billed : ∀ᶠ r in late, trueD U Y N Q r *ᵥ numbers (upgrade U Y d r a p)=trueLedger U Y N Q p a r := by
  filter_upwards [height (taking U J Y N hJ P M H h hp) (d+1),self_mem_nhdsWithin] with r h hr
  unfold trueLedger trueD; rw [← mulVec_mulVec]; congr 1; funext i; exact departing U Y N Q p a i hr h
lemma reserve (i j:Toon G (d+1)) : Worth late t δ (fun r=>trueD U Y N Q r i j) (speeds N Q i j) := fun m=> by
  simp_rw [speeds,trueD, Matrix.mul_apply]; exact Coin.sum (one_paid _) fun k (_:k∈(Finset.univ:Finset Q.axis))=>
    worth_mul (candidate_fee N t M H (Pose.guaranteed U J hJ N hp M H h)) (g0_zero sim) (Coin.literal _ (Fare.constant _)) (true_coin U J Y N hJ P M H h hp k.val.1 (levy k.val (theory j)) m)
lemma size (i:Toon G (d+1)) : Worth late t δ (fun r=> coord i (upgrade U Y d r a p)) (sizeIt N Q p a i) := by
  apply solution (candidate_fee N t M H (Pose.guaranteed U J hJ N hp M H h)) (g0_zero sim) (nominal N Q) (reserve U J Y N hJ P M H h hp Q) (fun r=> trueLedger U Y N Q p a r) _ (billed U J Y N hJ P M H h hp Q p a) i
  intro i m; unfold earned; exact Coin.sum (one_paid _) fun k (_:k∈(Finset.univ:Finset Q.axis))=>
    worth_mul (candidate_fee N t M H (Pose.guaranteed U J hJ N hp M H h)) (g0_zero sim) (Coin.literal _ (Fare.constant _)) (true_coin U J Y N hJ P M H h hp (shiftT 0 a k.val.1) (levy k.val (up (Nat.le_succ _) p)) m)
end YM.FVA2.GradedFar259.Sparks
