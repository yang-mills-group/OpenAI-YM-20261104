import YM.Integration.FVA1Physical.TwoReset.Copies
import YM.Integration.FVA1Physical.TwoReset.FiniteClubs
import YM.QuadraticLocal.Fk.Window

/-! Repeated input. Power of g held with the letter, and restored at reading.
Include all the inherited analytic vacuum packets at the step. Applies AFTER realignment:
the analytic model supplied to the prescription is the full unmasked one. -/

set_option autoImplicit false
set_option maxHeartbeats 880000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] {c f n : Side}
  {J : Passport n V} {R : Census V}
variable (h : n.val ∣ f.val) (M : ι→Row J R G α) (w : V→ℕ) (q : ι→ℂ)
    (L : Layout G) (T : Finset Age)

/-- Canonical powered letter summed over its repeat. -/
def copiesLetter (j : ι) (x : ℝ) (U : Config G f) : ℂ :=
  ∑ y ∈ parcel (splitter h) (M j).center, Complex.ofReal
    (Loan.letter (M j).lamp (M j).atom y x U)

local notation "ι'" => Fin (Pages n f)
local notation "M₁" u:max => (fun j:ι=> TwoReset.copy h (M j) u)
local notation "M₂" => copiesLetter h M
local notation "fee" => (fun i:Multi.Hot R => Launch.index R w i.val + 1)

noncomputable abbrev finiteColor (F : Finset ι) :=
  LinearLetters.colors F (QuadraticLocal.Fk.money L T) (copiesLetter h M) R
    (ScatterR.actor M) q fee

/-- Color input for the whole repeated packet. Not taking q from any actual output
error or old packet valuation. -/
noncomputable def copyColor : Colors R G f := {
  vac := QuadraticLocal.Fk.money L T, power := fee
  mark i := ∑ u:Fin (Pages n f), (Air.craft (M₁ u) q w L T).mark i }

lemma salaries (j:ι) : q j • M₂ j = ∑ u: Fin (Pages n f), ScatterR.familyAt (M₁ u) q j := by
  funext x U
  unfold copiesLetter
  simp only [Pi.smul_apply,Finset.sum_apply]
  rw [← pages h (M j).center (fun y=> Complex.ofReal (Loan.letter _ _ y x U)),Finset.smul_sum]; rfl

lemma colors_copy_mark (F : Finset ι) (i : Multi.Hot R) :
    (finiteColor h M w q L T F).mark i = ∑ u: Fin (Pages n f),
      (ScatterR.colors (M₁ u) F L T R (ScatterR.actor (M₁ u)) q w).mark i := by
  unfold finiteColor LinearLetters.colors
  simp_rw [ScatterR.markEq,salaries]
  exact Finset.sum_comm

local notation "Y₂" => copyColor h M w q L T

variable {a : ℝ} {k : ℕ} (hu : Air.Staff M q w a k)
include hu
local notation "U'" => Config G f
lemma copy_staff (j:ι') : Air.Staff (M₁ j) q w a k :=
  ⟨hu.entering,hu.written,hu.lamps,hu.couplings,hu.payment⟩

/-- In particular no question of differentiating a nonsummable copy packing. -/
lemma copy_standard (he : Legal T L) : (copyColor h M w q L T).Standard := by
  let X (u:ι') := Air.craft (M₁ u) q w L T
  let F := copyColor h M w q L T
  have H u : (X u).Standard := Air.standard (M₁ u) q w (copy_staff h M w q hu u) L T he
  refine ⟨⟨(QuadraticLocal.Fk.level L T he).lower (by decide),?_, fun t=> (QuadraticLocal.Fk.budget L T he t).varnish,
    ?_,fun t=>(QuadraticLocal.Fk.budget L T he t).fit,?_⟩,QuadraticLocal.Fk.level L T he⟩
  · intro i
    change Assembly.GradeAt (F.power i) (projected (∑ u:ι', (X u).mark i))
    unfold projected
    simp_rw [Finset.sum_apply]; apply Assembly.GradeAt.list_sum
    intro u _
    exact (H u).1.suppose_mark i
  · intro i g t z
    change (∑ u:ι',(X u).mark i) g _ =(∑ u:ι',(X u).mark i) g _
    simp_rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun u _=> (H u).1.gauges i g t z)
  intro i t
  change Envelope ((∑ u:ι',(X u).mark i) t)
  rw [Finset.sum_apply]
  rw [show ∑ u:ι',(X u).mark i t = (fun x=> ∑ u:ι',(X u).mark i t x) from funext fun x=>
    Finset.sum_apply x _ _]
  exact RG.Envelope.sumC _ _ (fun u _=> (H u).1.prices i t)

variable {S : StepData c f} {P : Clip} {Y : PathData G} {O : ChartRatio G}
variable (K : Kernel S P Y O) (A : Forest S.ratio) (t : S.Choices)
    (x : Exterior.fieldDir G c 1) (r i : ℕ)

omit hu in
lemma posed_copies_smooth (j:ι) : ContDiffAt ℝ ω (Bulk.posed S A (M₂ j)) 0 := by
  unfold Bulk.posed copiesLetter
  apply ContDiffAt.sum
  intro x hx
  let g := fun t U => Complex.ofReal (Loan.letter (M j).lamp (M j).atom x t U)
  exact (Bulk.joint_receipt S A (z:=g) ((Loan.frame (M j).lamp (M j).atom x).linear_contact
    Complex.ofRealCLM)).smooth

variable [Fintype V]

theorem copied_output : Tendsto (fun F:Finset ι => Order.observe R r
    (Order.logMarked (Bulk.Fk K A t (finiteColor h M w q L T F) x r)) i)
    atTop (𝓝 (Order.observe R r (Order.logMarked (Bulk.Fk K A t Y₂ x r)) i)) := by
  let f (F:Finset ι) := finiteColor h M w q L T F
  let Y := copyColor h M w q L T
  let C (u:ι') := M₁ u
  let U (u:ι') (F:Finset ι) := ScatterR.colors (C u) F L T R (ScatterR.actor (C u)) q w
  let X (u:ι') := Air.craft (C u) q w L T
  apply ((Order.observeL (R:=R) (r:=r) i).continuous_of_finiteDimensional.tendsto _).comp
    ((WickLimit.always_marked.tendsto _).comp (_ : Tendsto (fun F=> Bulk.Fk K A t (f F) x r)
      atTop (𝓝 (Bulk.Fk K A t Y x r))))
  refine WickLimit.survey _ _ _ _ K A f Y t x (fun _=>rfl) (fun _=>rfl) ?_
  intro s d z
  have hh u : Tendsto (fun F:Finset ι => iteratedFDeriv ℝ d (Bulk.markFn S A (U u F) s) 0 z)
      atTop (𝓝 (iteratedFDeriv ℝ d (Bulk.markFn S A (X u) s) 0 z)) :=
    Air.convergence (C u) q w (copy_staff h M w q hu u) L T s A d z
  have he (F:Finset ι) : Bulk.markFn S A (f F) s = ∑ u:ι', Bulk.markFn S A (U u F) s := by
    funext v
    unfold markFn Bulk.posed
    rw [show (f F).mark s = _ from colors_copy_mark h M w q L T F s]
    simp only [Finset.sum_apply]; rfl
  have hk : Bulk.markFn S A Y s = ∑ u:ι', Bulk.markFn S A (X u) s := by
    funext v
    unfold markFn Bulk.posed Y copyColor
    simp only [Finset.sum_apply]; rfl
  have hm u F : ContDiffAt ℝ ω (Bulk.markFn S A (U u F) s) 0 := by
    unfold markFn Bulk.posed U
    rw [show (ScatterR.colors _ _ _ _ _ _ _ _).mark s=_ from ScatterR.markEq (C u) F L T R (ScatterR.actor (C u)) q w s] -- adapt lambda
    simp_rw [Finset.sum_apply]
    exact ContDiffAt.sum fun i _=> (Bulk.joint_receipt S A (ScatterR.mature (C u) q i)).smooth
  have hj (u:ι') : ContDiffAt ℝ ω (Bulk.markFn S A (X u) s) 0 := (Bulk.joint_receipt S A
    (Air.grade (C u) q w (copy_staff h M w q hu u) L T s)).smooth
  rw [hk,iteratedFDeriv_sum_apply (fun u _=> (hj u).of_le le_top),_root_.sum_apply]
  simp_rw [he,iteratedFDeriv_sum_apply (fun u _=> (hm u _).of_le le_top),_root_.sum_apply]
  exact tendsto_finsetSum _ (fun u _=> hh u)
end YM.Integration.FVA1Physical.TwoReset
