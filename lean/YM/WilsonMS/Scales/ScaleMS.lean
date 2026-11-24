import YM.WilsonMS.Scales.ClockH
import YM.WilsonMS.Scales.LogPolygon
/-!
# Dilation and log polynomial of the literal continuum MS amplitudes

Include passage through IR. `t` increases when measuring smaller physical
distances; `sweep` acts where actual comparison holds, i.e. only separated
points, includes engineering factor already.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open MS MS.Plane MS.Koszul MS.Latch MS.Latch.Job MS.Tone MS.Landau.Detect MS.Land
open MS.Rake MS.Vane MS.Tide MS.Dial MS.Fleet MS.Local.Physical MS.Logarithm Rake.Geo
open MS.Menus MS.Theater
open XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open Fiscal BMenu VisitH FrameConj Sea TraceMC
open PowerSeries (coeff mk X C constantCoeff)
open Puff Actors Puff.Engine Puff.Mom
open scoped BigOperators Topology Classical
variable {G : Gauge} {A : Deck G} {M : Booked A} {μ : ℝ} {n d : ℕ}
section Native
variable {W : Type} [LinearOrder W] (F : MS_Data G M) {p : W → Label A} {x : W → QP}

lemma lift_book (hx : Injective x) (s : Finset W) (r : ℝ) (n : ℕ) :
    book F p μ (fun w => exp r • x w) s n =
      Port.τ (-(Vane.charge (Label.h ∘ p) s : ℤ)) r * book F p (μ + r) x s n := by
  let U := spine F p μ (fun w => exp r • x w)
  let Y := spine F p (μ + r) x
  have ht := pin F p μ ((smul_right_injective QP (exp_pos r).ne').comp hx)
  have he := pin F p (μ + r) hx
  apply congr_fun (Port.MoonB F (σ := fun (_ : Unit) => r) (fun _ => rfl) he ht s n ?_) ()
  intro i
  obtain hp | hL := s.eq_empty_or_nonempty
  · rw [hp, he.1]
    exact (Fleet.allow_zero i).1
  have hV : Rake.Mesh (frameF Unit (μ + r)) (fun w _ => x w) := by
    intro y z hy
    have hx : 0 < ‖x y - x z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne hy))
    refine ⟨⟨_, hx, fun _ => ?_⟩, ⟨_, hx, fun _ => ?_⟩⟩ <;> simp [roots]
  exact (reports p hV he hL n).1 i

lemma lift_tour (hx : Injective x) (s : Finset W) (r : ℝ) (n : ℕ) :
    tour F p μ (fun w => exp r • x w) s n =
      Port.τ (-(Vane.charge (Label.h ∘ p) s : ℤ)) r * tour F p (μ + r) x s n := by
  let Q := Trunk.stack (Puff.SplitP.marked W)
  let a (k : Finset W) := Port.τ (-(Vane.charge (Label.h ∘ p) k : ℤ)) r
  let L : Module.End ℂ (Finset W → Book.Convolve.T ℂ) :=
    { toFun x k := a k • x k
      map_add' x y := funext fun i => smul_add (a i) (x i) (y i)
      map_smul' c x := funext fun i => smul_comm (a i) c (x i) }
  have hL : Tether L Q Q := by
    refine ⟨funext fun i => ?_, fun x y => funext fun u => ?_⟩
    · change a i • (Puff.SplitP.marked W).refineV Trunk.unit i = _
      by_cases h : i = ∅
      · subst i
        simp [a, Vane.charge, Port.τ]
        rfl
      change _ = (Puff.SplitP.marked W).refineV Trunk.unit i
      rw [Puff.SplitP.refineV, if_neg (show i ≠ (Puff.SplitP.marked W).origin from h), smul_zero]
    change
      a u • ((Puff.SplitP.marked W).Lift Trunk.core x y u) =
        (Puff.SplitP.marked W).Lift Trunk.core (L x) (L y) u
    simp_rw [Puff.SplitP.loan, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hv : a u = a k.1 * a k.2 := by
      rcases k with ⟨K, S⟩
      obtain ⟨ha, hb⟩ := Puff.SplitP.joins.mp hk
      unfold a Vane.charge
      rw [Port.T_add, ← ha, Finset.sum_union hb, Nat.cast_add, neg_add]
    rw [hv]
    change _ = Trunk.core (a k.1 • x k.1) (a k.2 • y k.2)
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  unfold tour
  let S := Dial.book F p (μ + r) x
  rw [show Dial.book F p μ _ = L S from funext fun s => funext fun n => lift_book F hx s r n]
  exact congr_fun (congr_fun ((hL.cheersV s.card S).symm) s) n
end Native
local notation "BΨ" => Ensure.deck G
variable {Y : Booked (Ensure.deck G)} (F : MS_Data G Y) (μ r : ℝ)

def GMS (d : ℕ) : ChartK G d := fun _ p k => lowKernel F μ k d p

def Rigid (d : ℕ) : ChartK G d := fun _ p i => if i = 0 then scene p d else 0

lemma coupon_stage (d n : ℕ) : FundsK (GMS F μ d n) (fun i => Continuum F μ i d) := fun i p =>
  ⟨smooth_read F μ i p, fun _ => continues ..⟩

lemma starClock (d : ℕ) : Equad (sweep r (GMS F μ d)) (GMS F (μ - r) d) := by
  intro n x hx
  funext i
  ext1 p
  rw [fromHeight, fromHeight ((GMS F (μ - r) d n x i))]
  apply Finset.sum_congr rfl
  intro w hw
  apply congr_arg
  rw [exact_sweep]
  rw [show ((window G d r) ∘ (glow ∘ w)) = (fun i => tag r (w i).size • glow (w i)) from
      funext fun i => pane_g r _]
  unfold GMS
  let t := -r
  simp_rw [show ∀ (q : Sec G d) (x : ℝ), x • q = (x : ℂ) • q from fun x z =>
      (IsScalarTower.algebraMap_smul ℂ z x).symm,
    MultilinearMap.map_smul_univ]
  change _ • lowKernel F μ _ _ _ (glow ∘ w) = _
  rw [lowK, lowK]
  unfold answers
  rw [show VisitH.actual (pullT r x) = fun i => exp t • actual x i from
      funext fun i => by
        unfold actual
        exact map_smul Theater.out (exp t) (x i),
    lift_tour F (act_inj x hx)]
  rw [show μ + t = μ - r from rfl]
  let p := ∏ i, (tag r (w i).size : ℂ)
  let d' : ℤ := Vane.charge (Label.h ∘ profileK w) Finset.univ
  rw [smul_eq_mul, ← mul_assoc, show p * Port.τ (-d') t = 1 from ?h, one_mul]
  have he :
    ∀ s : Finset (Fin n),
      ∏ i ∈ s, (tag r (w i).size : ℂ) = Port.τ (Vane.charge (Label.h ∘ profileK w) s) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Vane.charge, Port.τ]
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, ih,
        show Vane.charge (Label.h ∘ profileK w) _ = (w i).size + Vane.charge (Label.h ∘ profileK w) s
          from Finset.sum_insert hi,
        Nat.cast_add, ← Port.T_add, tag, Real.exp_nat_mul]
      rfl
  unfold p
  rw [he, Port.T_add, show (_ : ℤ) + -d' = 0 from add_neg_cancel _]
  simp [Port.τ]

lemma rooted_flow (d : ℕ) (n : ℕ) (x : Points n) (hx : x ∈ conf n) : GMS F μ d n x 0 = scene x d := by
  ext1 p
  exact leadingPoint F μ hx p
end YM.WilsonMS.GFlow
