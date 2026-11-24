import YM.WilsonMS.Scales.Polo
/-!
# One compatible mass-independent adjustment

Choose the strict tilings; prove their defining property (including the
entire upright `B_t` from the scaled X array). No order-dependent tests
or fields used as second set of independent data. The formula uses the MS
comparison but uniqueness will characterize from Wilson, after identifying
it intrinsically.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G

structure Traveling (G : Gauge) where
  Q : ℝ → Links G
  r : ℝ → Cn

def compass (t : ℝ) (c : Cn) (B : Guard G d) (N : Guard G d) :=
  vault (buryD t N) * B * coupon c N

structure Anchored (A : Traveling G) (N : Guard G d) : Prop where
  nearN : CloseP N
  strict : PureDrop N
  grade : ∀ s : ℝ, Mass (compass s (A.r s) (A.Q s d) N)

abbrev revising (P : Scheme G) (N : Links G) : Scheme G := fun d => Act (P d) (N d)

lemma strict_moves {V : Scheme G} {B : Links G} {T : Links G} {U : Cn} {s : ℝ} (h : ∀ d, CloseP (B d))
    (ht : Linked V s T U) : Linked (revising V B) s (fun d => compass s U (T d) (B d)) U := by
  refine
    ⟨fun d => ((duties s (h d)).invert.times (ht.ground d)).times ((h d).substitute ht.normal.clean),
      ht.normal, fun d => ?_⟩
  unfold revising
  rw [adjoint, action_times, compass, ← mul_assoc (buryD s _) (_ * _) _, ← mul_assoc,
    (antidote (duties s (h d))).1, one_mul, ← action_times (sweep s (V d)), action_sub ht.normal.root]
  exact Equad.act (ht.origin d) _
variable {M : Booked (Ensure.deck G)} {F : MS_Data G M} {V : Store G} (P : Rose.Pick V) {t r : ℝ}
  {W : Initialize G}

abbrev tripX (P : Rose.Pick V) (F : MS_Data G M) : Traveling G :=
  ⟨changeM P F, transit P F⟩

abbrev FrontMS (P : Rose.Pick V) (F : MS_Data G M) (d : ℕ) : Guard G d :=
  coupon (ψW P F) (KnotMS F V 0 d)

abbrev Zx (P : Rose.Pick V) (F : MS_Data G M) (d : ℕ) : Guard G d :=
  printM (FrontMS P F d)

def uprightN (P : Rose.Pick V) (F : MS_Data G M) (d : ℕ) :=
  vault (FrontMS P F d) * Zx P F d

def finale (P : Rose.Pick V) (F : MS_Data G M) : Scheme G :=
  revising (ΨScheme P F) (uprightN P F)

abbrev β_frame (P : Rose.Pick V) (F : MS_Data G M) (t : ℝ) : Links G := fun d =>
  compass t (transit P F t) (changeM P F t d) (uprightN P F d)
variable (hG : G.Simple) {X : Prescription (Ensure.deck G)} (hp : Installed W F X) (hh : Commuting X)
include hG hp hh

lemma front_close (d : ℕ) : CloseP (FrontMS P F d) :=
  (knot_base F V 0 d).substitute (ψ_aware P hG hp hh).clean

lemma neutral (d : ℕ) : CloseP (Zx P F d) :=
  printH (front_close P hG hp hh d)

lemma freeN (d : ℕ) : CloseP (uprightN P F d) :=
  (front_close P hG hp hh d).invert.times (neutral P hG hp hh d)

lemma recallZ : (fun d => Zx P F d) = (fun d => FrontMS P F d * uprightN P F d) := by
  funext d
  unfold uprightN
  rw [← mul_assoc, (antidote (front_close P hG hp hh d)).1, one_mul]

lemma cN : Connect (uprightN P F) := fun d =>
  Ladder.product
    (Ladder.turnback ((layout_fit F V 0 d).edit _) (front_close P hG hp hh _)
      (front_close P hG hp hh _))
    (ladder_tile ((layout_fit F V 0 d).edit _))

omit hG hp hh in
lemma cnZ (F : MS_Data G M) : Connect (Zx P F) := fun d => ladder_tile ((layout_fit F V 0 d).edit _)

lemma Ck (d : ℕ) : finale P F d = Act (Sub (ψW P F) (GMS F 0 d)) (Zx P F d) := by
  unfold finale revising
  rw [show ΨScheme P F d = Act (Sub (ψW P F) (GMS F 0 d)) (FrontMS P F d) from
      Eq.trans rfl (action_sub (ψ_aware P hG hp hh).root _ _),
    action_times]
  exact congr_arg _ (congr_fun (recallZ P hG hp hh) d).symm

lemma kinetic (t : ℝ) : Linked (finale P F) t (β_frame P F t) (transit P F t) :=
  strict_moves (B := uprightN P F) (freeN P hG hp hh) (growth P hG hp hh t)

lemma purity (d : ℕ) : Lines (finale P F d) := by
  rw [Ck P hG hp hh]
  exact ((global_P F 0).subs (ψ_aware P hG hp hh).root).pulls Mass.print
omit hG hp hh

lemma step_K {T : Guard G d} {V : ChartK G d} (h : CloseP T) (x : Points n) :
    Act V T n x 0 = V n x 0 := by
  ext1 i
  unfold Act
  rw [pivot_cost, Normalize.tally, Finset.finsuppAntidiag_zero, Finset.sum_singleton]
  exact
    congr_arg _
      (funext fun k => by
        unfold pulseU
        rw [Finsupp.coe_zero, Pi.zero_apply, h.zeroC]
        rfl)
include hG hp hh

lemma prim_X (t : ℝ) (n d : ℕ) (x : Points n) (hx : x ∈ conf n) :
    sweep t (finale P F d) n x 0 = scene (G := G) x d := by
  rw [Ck P hG hp hh, adjoint, step_K (duties t (neutral P hG hp hh _)), ←
    name_sub _ (ψ_aware P hG hp hh).root, Sub, pay0, starClock F 0 t d n hx, rooted_flow F _ _ _ _ hx]

lemma grade_N (d : ℕ) : Anchored (tripX P F) (uprightN P F d) := by
  refine ⟨freeN P hG hp hh _, Strict (front_close P hG hp hh d), fun t => ?_⟩
  obtain h := kinetic P hG hp hh t
  refine power_mass hG (P := β_frame P F t d) (h.ground d) ((purity P hG hp hh d).spun t) ?_ ?_
  · exact ((purity P hG hp hh d).subs h.normal.root).pass (h.origin d).symm
  intro s n x hx
  rw [lands, prim_X P hG hp hh _ _ _ x hx]
end YM.WilsonMS.GFlow
