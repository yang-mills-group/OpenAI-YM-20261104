import YM.WiderProfiles.RawPrice
import YM.FVA2.Speed.Hearth
/-!
# Through the position solve

Use the actual power prices on the deck coefficients at the pivot (`Speed/Ports`,
`Cake.coast`). Expand on the same slots/bases as in `paints`. Here the operands at
those varying shapes need only be `Slow`, not bounded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State
open Speed Speed.Star Asymptotics Finset
open scoped Topology ContDiff BigOperators Classical

variable {n a d k : ℕ} {G : Gauge} {c D : ℝ}
local notation "ι" => Domain n a c D
local notation "ℓ" => along n a c D

/-- Shorthand for the uniform Bond on this family, mildG exponent. -/
abbrev Costing {n a : ℕ} {c D : ℝ} {E : Type*} [NormedAddCommGroup E]
    (x y : Domain n a c D → E) :=
  Bond (along n a c D) (fun i => Schedule.theta (grab i.val)) mildG x y

lemma sharp_bond {E : Type*} [NormedAddCommGroup E] {x y : ι → E}
    (h : Sharp (along n a c D) (fun i => grab i.val) x y) : Costing x y := by
  obtain ⟨C, hC, hq⟩ := Expense.Cap.bounds h.quote
  obtain ⟨b, hb, hw⟩ := Fast.bounds h.sails
  refine Bond.of_right (fun i => le_max_right ..) ⟨b, hb, 0, ?_⟩ (Price.bounded C hC hq) mild_p.le
  filter_upwards [hw] with i hi
  rw [Pi.sub_apply, height_cost i.val i.property.sized, pow_zero, mul_one]; exact hi

variable (μ : ℝ) (Y : XSpace.Initialize G) (V : Normalize.Store G)
    (A : Prescription (Press.portDeck G)) {O : Booked (Press.portDeck G)} (S : MS_Data G O)
    (h : G.Simple) (hs : TaylorOKF S (Press.wickInput Y) A)
variable (hc : 0 < c) (hD : 1 ≤ D)
include h hs

lemma deck_bond (n a : ℕ) (c D : ℝ) (p : Sec G d) (k : ℕ) :
    Costing (fun i : Domain n a c D => tableD G d
      (coeff k (deck (Pivot.chalk μ Y V A d (grab i.val))) p))
      (fun _ => tableD G d (coeff k (deck (State.root μ V S d)) p)) :=
  sharp_bond (Sharp.once (tended n a c D) (Sharp.above (prices frontier (Cake.coast μ Y V A S h hs) p k)))

include hc hD
lemma basis_bond (t : Fin n → Toon G d) (k : ℕ) (a : ℕ) :
    Costing (fun i : Domain n a c D => postedPoint μ Y A d i.val k (fill t))
      (fun i => meteor μ S d (familiar i.val) k (fill t)) := by
  simp_rw [ribbon, Dframe.reads]
  exact rawPrice μ Y _ A S h hs a c D hc hD _ k

lemma posted_bond (a : ℕ) (k : ℕ) (v : Tags G d n) :
    Costing (fun i : Domain n a c D => postedPoint μ Y A d i.val k v)
      (fun i => meteor μ S d (familiar i.val) k v) := by
  simp_rw [stencil_he (postedPoint μ Y A d _ _) v, stencil_he (meteor μ S d _ _) v]
  exact Bond.sum (fun i => le_max_right ..) _ _ _ (fun t _ =>
    Bond.mul (fun i => le_max_right ..) (Bond.const _ _ _ _) (basis_bond μ Y A S h hs hc hD t k a))

-- analogue of paints for varying-shape Bond (not Sharp)
omit h hs hc hD in
lemma paints_bonds (w : Domain n a c D → Pick G d) (v : Pick G d)
    (hp : FFrame ℓ (fun i : ι => grab i.val) w v)
    (x y : ι → ℕ → Structure1.Point G d n)
    (he : ∀ k (p : Tags G d n), Costing (fun i => x i k p) (fun i => y i k p))
    (k : ℕ) (p : Tags G d n) : Costing (fun i => status (deck (w i)) (x i) k p)
      (fun i => status (deck v) (y i) k p) := by
  simp_rw [seen, stencil_he ( x _ _ ) ( pulseU _ _ _ ), stencil_he ( y _ _ ) (pulseU _ _ _),sift]
  apply Bond.sum (fun i => le_max_right ..); intro l hl
  apply Bond.sum (fun i => le_max_right ..); intro j _
  refine Bond.mul (fun i => le_max_right ..) (Bond.prod (fun i => le_max_right ..) _ _ _ ?_) (he _ _)
  intro i _
  exact sharp_bond (Sharp.above (process (stretch n a c D)
    (p:=coeff (l (some i)) (deck v) (p i)) (prices (stretch ..) hp (p i) _) (j i)))

lemma coupled_bond (a : ℕ) (k : ℕ) (v : Tags G d n) :
    Costing (fun i : Domain n a c D => coupledPoints μ Y V A i.val d k v)
      (fun i => State.wall μ V S d (familiar i.val) k v) := by
  unfold coupledPoints State.wall State.chooseL
  let w := fun i : Domain n a c D => grab i.val
  have hp : FFrame (along n a c D) w (fun i => Pivot.chalk μ Y V A d (w i)) (State.root μ V S d) := by
    intro j
    have hx := Fast.comp w (tended n a c D) (Cake.coast μ Y V A S (d:=d) h hs j)
    exact hx
  exact paints_bonds _ _ hp
    (fun i => postedPoint μ Y A d i.val) (fun i => meteor μ S d (familiar i.val))
    (fun j p => posted_bond μ Y A S h hs hc hD a j p) k v

lemma cooked_bond (hr : Position.Favors.Horder A) (hu : Position.Ace.UnitP A)
    (a : ℕ) (k : ℕ) (v : Tags G d n) :
    Costing (fun i : Domain n a c D => substitute (Dframe.reset μ A (grab i.val))
        (Rose.cooked Y V d i.val) k v) (fun i => State.wall μ V S d (familiar i.val) k v) := by
  apply Bond.tee (coupled_bond μ Y V A S h hs hc hD a k v) _ (.refl ..)
  filter_upwards [(tended n a c D).eventually (Pivot.timely (d:=d) μ Y V A S h hs hr hu frontier)] with i hi
  rw [Pivot.whole μ Y V A _ hi]
end YM.FVA2.WiderProfiles
