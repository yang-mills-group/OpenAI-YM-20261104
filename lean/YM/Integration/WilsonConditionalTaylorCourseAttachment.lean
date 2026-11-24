import YM.Integration.WilsonConditionalTaylorRawAttachment

/-! Attaching the finite nonlinear bulk course and both measured scalar
coupling factors to all physically issued scenes on the original run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCourseAttachment
open Filter Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorBulkHistory WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorSceneCalibration
open WilsonMovingPolynomialPull WilsonConditionalTaylorRawAttachment
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
variable {N per k cap : ℕ} {S : Scene R.family.path.levels per cap}
variable (scene : Realized R.alloy.B.kin N per k cap (Lis.sun G u) S)

def placed (N per j : ℕ) := stored (course R u wood tags N j (R.family.side j per))
def price (N per j : ℕ) := WilsonConditionalTaylorBulkClock.field (Lis.sun G u) (R.alloy.B.kin.path N j)
  (R.family.path.levels.params j).clip (raw R wood tags N j (course R u wood tags N (j+1)) (R.family.side j per))

include simple scene in
theorem nextField (j : ℕ) (lo : k≤j) (hi : j<N)
    (bill : Alto.Sampled (R.family.side j per) (R.family.path.levels.params j))
    (previous : Fields cap (S.Poly (j+1)) (placed R u wood tags N per (j+1))) :
    Fields cap (S.Poly j) (placed R u wood tags N per j) ∧
      Through cap (S.action j) (bookU (price R u wood tags N per j)) ∧
      Through cap (S.action j)⁻¹ (bookH (price R u wood tags N per j)) :=by
  let V:=R.family.path.levels
  let n:=R.family.side j per
  let s:=(WilsonMovingGaussianCoordinates.link G n).symm
  let v:=Lis.sun G u
  let Z:=raw R wood tags N j (course R u wood tags N (j+1)) n
  let Q:=inkAt R N per j
  let T:=untuned R scene j lo hi
  let b:=S.action j
  let H:=price R u wood tags N per j
  let H':=WilsonConditionalTaylorSceneReset.measured R scene j lo hi
  obtain ⟨_,clear,receipt,_⟩:=WilsonConditionalTaylorSceneCalibration.received R scene j lo hi
  have income:=WilsonConditionalTaylorRawAttachment.step R u wood tags scene j lo hi previous
  have txn : Through cap H' H:=WilsonConditionalTaylorFieldBalance.owes v Q income
  have first : Fresh H':=WilsonConditionalTaylorKineticRebooking.head v T Q clear
  have second : Fresh H:=WilsonConditionalTaylorBulkClock.fresh ..
  have clock:=WilsonConditionalTaylorFieldBalance.clocks first second txn
  have selected:=WilsonConditionalTaylorSceneReset.original R scene j lo hi bill
  have forward : Through cap b (bookU H):=fun e he=>(selected.1 e he).trans (clock.2 e he)
  have backward : Through cap b⁻¹ (bookH H):=fun e he=>(selected.2 e he).trans (clock.1 e he)
  refine ⟨?_,forward,backward⟩
  have corpus:=WilsonConditionalTaylorCourseLedger.rawField R u wood tags N j hi n
  have native:=WilsonConditionalTaylorKineticHead.physical R simple wood u N j hi.le n
  have ground : coeff 0 (place s Z)= -Q:=by
    change MvPolynomial.rename s (coeff 0 Z) = -Wave.ink n (V.params j).clip (R.alloy.B.kin.path N j)
    rw [native,neg_neg,show coeff 0 Z=_ from corpus.1]
  have quadratic : Q.IsHomogeneous 2:=by
    change (Wave.ink n (V.params j).clip (R.alloy.B.kin.path N j)).IsHomogeneous 2
    rw [native]
    exact ((kinetic_grade _).rename_isHomogeneous).neg
  have outcome : Kind (Wave.bley b T Q) := by
    change coeff 0 (Wave.bley (S.action j) (untuned R scene j lo hi) (inkAt R N per j))=0
    rw [←receipt]
    exact (scene.budget j hi.le lo).1.bond
  have earned:=WilsonConditionalTaylorFieldReset.step b (bookH H) (bookU H) T (place s Z) Q clear outcome ground quadratic
    (WilsonConditionalTaylorFieldReset.transport corpus.2.1 s) income backward forward
  unfold placed
  rw [next R u wood tags N j hi,receipt]
  change Fields cap (Wave.bley b T Q) (splitV (place s (canter (bookH H) (bookU H) _ Z)))
  rw [WilsonConditionalTaylorResetCoordinates.permuted]
  exact earned

include simple scene in
theorem sceneField (bill : ∀ j ≤ N, Alto.Sampled (R.family.side j per) (R.family.path.levels.params j))
    (j : ℕ) (age : j≤N) : k≤j → Fields cap (S.Poly j) (placed R u wood tags N per j) :=by
  induction age using Nat.decreasingInduction with
  | self =>
    intro _
    rw [scene.opening]
    exact fromPrefix (fun e _=>congrArg (coeff e) (WilsonConditionalTaylorCourseLedger.opening R u wood tags N (R.family.side N per)))
  | of_succ i hi ih =>
    intro lo
    exact (nextField R simple u wood tags scene i lo hi (bill i hi.le) (ih (by omega))).1

include simple in
theorem issued (N cap : ℕ) : ∀ᶠ per:ℕ in atTop,
    ∀ k, ∀ S:Scene R.family.path.levels per cap, Realized R.alloy.B.kin N per k cap (Lis.sun G u) S →
      ∀j, k≤j → j≤N → Fields cap (S.Poly j) (placed R u wood tags N per j) ∧
        (j<N → Through cap (S.action j) (bookU (price R u wood tags N per j)) ∧
          Through cap (S.action j)⁻¹ (bookH (price R u wood tags N per j))) :=by
  filter_upwards [WilsonConditionalTaylorCourseLedger.sampled R N] with per finance k S held j lo hi
  refine ⟨sceneField R simple u wood tags held finance j hi lo,?_⟩
  intro step
  exact (nextField R simple u wood tags held j lo step (finance j hi)
    (sceneField R simple u wood tags held finance (j+1) step (by omega))).2

end YM.Integration.WilsonConditionalTaylorCourseAttachment

