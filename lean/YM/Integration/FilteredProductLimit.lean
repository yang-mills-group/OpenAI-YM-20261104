import YM.Integration.FilteredWilsonProduct
import YM.Integration.WilsonWholeLimitRoom

/-! Equality of the extracted physical product before and after exact
filtration resolution. All slots and the spectators use the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FilteredProductLimit
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit ActualFoundryDetectorSource
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {e : E → ℕ} {D : ℕ}

private theorem change_slots {X : Type*} {K : Type} [Fintype K] (f : (K → X) → ℂ)
    (v w : K → X) (slots : ∀ i a, f (update a i (v i)) = f (update a i (w i))) : f v = f w := by
  let g (s : Finset K) (i : K) := if i ∈ s then v i else w i
  have same (s : Finset K) : f (g s) = f w := by
    induction s using Finset.induction_on with
    | empty => simp only [g,Finset.notMem_empty,ite_false]
    | @insert i s hi ih =>
      have ha : g (insert i s) = update (g s) i (v i) := by
        funext k
        by_cases he : k = i
        · subst k; simp [g]
        · simp [g,he]
      have hb : update (g s) i (w i) = g s := by
        funext k
        by_cases he : k = i
        · subst k; simp [g,hi]
        · exact update_of_ne he ..
      rw [ha,slots,hb,ih]
  simpa only [g,Finset.mem_univ,ite_true] using same Finset.univ

/-- A separated table moment is invariant under all actual filtration
inclusions, with each slot changed on the same hierarchy. -/
theorem moment_rise (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {a m : I → ℕ} (h : a ≤ m) (v : Labels S a) (x : I → E4) (hx : Injective x) :
    Orbits.moment S x (fun i => F.sector.derivatives.rise (h i) (v i)) = Orbits.moment S x v := by
  rw [observed,observed]
  apply change_slots
  intro i A
  apply observe_replace S A R.continuum.laws.toSymmetric (fun _ => le_rfl) R.lifts hx i (h i)
  change F.sector.derivatives.rise (h i) (S.project _ (S.representative _ (v i))) =
    S.project _ (S.representative _ _)
  rw [S.rep,S.rep]

def sector (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (g : Grades d) (i : I) : S.Field (levels g i) :=
  R.cutTest (levels g i) (d i) (J t (d i) (v i))

theorem continuum (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (x : I → E4) (y : E → E4) (w : Labels S e) (hx : Injective (beside x y)) :
    whole S x (PhysMS.Frame.born J t v) y w =
      ∑ g : Grades d, whole S x (sector F R J v t g) y w := by
  let Q := F.sector.derivatives
  let part (i : I) (k : Fin (d i+1)) := R.cutTest k.val (d i) (J t (d i) (v i))
  let lift (i : I) (k : Fin (d i+1)) := Q.rise (Nat.le_of_lt_succ k.isLt) (part i k)
  have expand : PhysMS.Frame.born J t v = fun i => ∑ k, lift i k := by
    funext i
    change J t (d i) (v i) = ∑ k, Q.rise _ (R.cutTest _ _ _)
    rw [R.reconstruct _ _ le_rfl,Q.arrival R.continuum.laws.toSymmetric R.lifts]
  let M : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ := sectionLabels (d:=Sum.elim d e) w (Orbits.moment S (beside x y))
  have placed (u : Labels S d) : M u = whole S x u y w := sectionLabels_apply ..
  rw [← placed,expand,M.map_sum lift]
  apply Finset.sum_congr rfl
  intro g _
  rw [placed]
  let deg : I ⊕ E → ℕ := Sum.elim (levels g) e
  have hc : deg ≤ Sum.elim d e := by
    rintro (i|j)
    · exact Nat.le_of_lt_succ (g i).isLt
    · exact le_rfl
  let low := stages (sector F R J v t g) w
  have hu : (fun i => Q.rise (hc i) (low i)) = stages (fun i => lift i (g i)) w := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact Q.arrival R.continuum.laws.toSymmetric R.lifts _
  unfold whole
  rw [← hu]
  exact moment_rise F R hc low (beside x y) hx

def raw (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) :=
  product (fun i => C.S.gridPoint j (x i)) (PhysMS.Frame.born J t v) w.1 w.2

private theorem detector_product (U : Detector S D) (i : Fin U.size) (w : ℕ × ℕ) :
    listen U i w = product (OPE.positions S (U.listen i)).ofLp
      (fun k => (tags S (U.listen i) k).2) w.1 w.2 := by
  funext X
  simp only [FilteredWilsonProduct.listen, Finset.prod_apply]
  rfl

private theorem grid_product {a : I → ℕ} (j : ℕ) (x : I → Cover) (v : Labels S a)
    (w : ℕ × ℕ) (live : j ≤ w.1) :
    leaves C j a x (fun i => S.representative _ (v i)) w.1 w.2 =
      product (fun i => C.S.gridPoint j (x i)) v w.1 w.2 := by
  have zero : ceilSite C w.1 w.2 (0:E4) = 0 := by
    change Lattice.wrap _ (fun _ => ⌈(0:ℝ)/C.S.a w.1⌉) = 0
    simp only [zero_div,Int.ceil_zero]
    exact (Lattice.wrap _).map_zero
  have sample (y : Cover) : ceilSite C w.1 w.2 (C.S.gridPoint j y) = location C.S j w.1 w.2 y := by
    simpa only [zero_add,zero] using WilsonExteriorGeometry.ceilSite_add_grid (C:=C) (p:=w.2) live (0:E4) y
  funext V
  simp only [leaves,Finset.prod_apply,product,sample]
  rfl

/-- The measured difference between the undivided born input and the
exactly resolved original field, with every specified exterior detector. -/
def difference (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (i : Fin U.size) :=
  moment (C.beta w.1 w.2) (raw J v t j x w * listen U i w) -
  moment (C.beta w.1 w.2) (field F R J v t j x w * listen U i w)

theorem difference_tendsto (F : Spec.Final C f S) (facility : Services C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (U : Detector S D)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover)
    (hx : ∀ i, Injective (beside (fun k => C.S.gridPoint j (x k)) (OPE.positions S (U.listen i)).ofLp)) :
    Tendsto (difference F R U J v t j x) f.fuse (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  let p (k : I) := C.S.gridPoint j (x k)
  let y := (OPE.positions S (U.listen i)).ofLp
  let w := fun k => (tags S (U.listen i) k).2
  let limit := whole S p (PhysMS.Frame.born J t v) y w
  have original : Tendsto (fun e : ℕ × ℕ => moment (C.beta e.1 e.2) (raw J v t j x e * listen U i e))
      f.fuse (𝓝 limit) := by
    apply (WilsonWholeLimit.whole_tendsto_separated F facility p (PhysMS.Frame.born J t v) y w (hx i)).congr'
    filter_upwards with k
    apply congrArg (moment (C.beta k.1 k.2))
    funext V
    rw [detector_product,WilsonWholeLimit.product_split]
    rfl
  have gathered : Tendsto (fun e : ℕ × ℕ => moment (C.beta e.1 e.2) (field F R J v t j x e * listen U i e))
      f.fuse (𝓝 limit) := by
    dsimp only [limit]
    rw [continuum F R J v t p y w (hx i)]
    apply (tendsto_finsetSum Finset.univ (fun g _ =>
      WilsonWholeLimit.whole_tendsto_separated F facility p (sector F R J v t g) y w (hx i))).congr'
    filter_upwards [(Cards.largeMesh f).eventually_ge_atTop j] with k live
    let az (g : Grades d) := product (beside p y) (stages (sector F R J v t g) w) k.1 k.2
    have eq (g : Grades d) : az g = leaves C j (levels g) x (component F R J v g t) k.1 k.2 * listen U i k := by
      change _ = leaves C j (levels g) x (fun n => S.representative _ (sector F R J v t g n)) k.1 k.2 * _
      rw [grid_product j x (sector F R J v t g) k live,detector_product]
      exact funext (WilsonWholeLimit.product_split p (sector F R J v t g) y w k.1 k.2)
    have expanded : field F R J v t j x k * listen U i k = ∑ g, az g := by
      rw [field_expansion,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun g _ => (eq g).symm)
    change ∑ g, moment (C.beta k.1 k.2) (az g) = _
    rw [expanded]
    unfold Wilson.moment
    simp only [Finset.sum_apply]
    exact (integral_finsetSum _ (fun g _ => product_integrable _ _ k.1 k.2)).symm
  simpa only [difference,sub_self,Pi.zero_apply] using original.sub gathered

end YM.Integration.FilteredProductLimit
