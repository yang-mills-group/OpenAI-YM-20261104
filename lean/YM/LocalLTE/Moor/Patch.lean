import YM.LocalLTE.Moor.Stamp
/-! Offer gluing using authentic barony Harbour, with detector HEAD
as predicted. Input prediction F_i (
 E6 term U equals ***negative*** predicted analytic fee) always full T.
 Booking keeps real lengths and positions on the physical calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Patch
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Trio Inset Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L:Side} {j i m n W w r k l z:ℕ} (B : BudgetPoint) {Y: Stars→ Side}
variable {f₀ : Offer G c} (fa:∀ i:Stars,Offer G (Y i)) (Q:∀ i:Stars,(Y i).val=2*(w+i.val))

def read (Y: Stars→Side) (G:Gauge) := ∀ i, Config G (Y i) →ℝ
variable (p : Patch.read Y G) (h: w+4 ≤ z)

def mural (o:Site c) := ∑ j:Stars, Slide.ray j • ((Boulevard.stillA (p j)) ∘ Slide.shape (Trio.pad Q j) o)
def light (y:Site c) := Trio.ornament Q fa y + mural Q p y -- order arguments

variable (x : Site c) (hf: ∀ i,B.Regular univ (p i))
include hf h
lemma regular : B.Regular (neighbors z x) (mural Q p x) := by
  unfold mural; refine Meadow.regularA _ (fun i hi=> CouplingShape.reg_scale _ (Slide.regular _ _ (f:=Boulevard.stillA _) (CouplingShape.reg_sub (hf i) (CouplingShape.reg_const _)) (fun j=> (neighbors_mem ..).2 ?_)))
  have ht := Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge x j; have hk:= i.isLt; apply ht.trans; omega
lemma localLight (he: ∀ i,B.Regular univ (Trio.froth (fa i))) : B.Regular (neighbors z x) (light fa Q p x):= by
  unfold light; rw [show (mural Q p x)=-((-1:ℝ) • mural Q p x) by simp,← sub_eq_add_neg]; refine CouplingShape.reg_sub ?_ (CouplingShape.reg_scale _ (regular B Q p h x hf)) -- order fac
  rw [Trio.orchard]; exact Patch.regular B Q _ h x he

omit hf
lemma pay_patch {q : Stars→ℝ} {e a:ℝ} (hq:∀ i,0 ≤ q i)
    (hf:∀ i,B.Regular univ ((Trio.froth (fa i))+p i))
    (he:∀ V: Config G c, Healthy B.threshold (neighbors z x) V→ ∀ i, ∃ (u:Site (Y i)→G.El) (P:Positions (Uniform.Primary (Y i) G)), actual P= gauge u (Slide.shape (pad Q i) x V)∧ ‖P‖+2*e <a)
    (hM: ∀ i (P : Positions (Uniform.Primary (Y i) G)),flags B.threshold (actual P)=∅→ ‖P‖+2*e < a → ∀ l: List (Directions G (Y i)),l.length ≤B.order→ (∀ v∈l, ‖v‖≤B.threshold)→ ‖leftDerivs (Boulevard.stillA ((Trio.froth (fa i))+p i)) l (actual P)‖ ≤ q i) :
    B.supBounds x (neighbors z x) (light fa Q p x) (Trio.oroW B z q):= by
  let f i:= (Trio.froth (fa i))+p i
  let w': ∀ i:Stars,Offer G (Y i):= fun i x=> if x=0 then f i else 0
  have hW i: Trio.froth (w' i)= f i:= by ext V; unfold Trio.froth w'; rw [sum_eq_single (0:Site (Y i))]; simp; exact (fun i _ hv=>by simp [hv]); simp
  have hp : Patch.light fa Q p x = Trio.ornament Q w' x:=by
    unfold Patch.light; rw [Trio.orchard,Trio.orchard]
    unfold Patch.mural; ext V; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Function.comp_apply, ← sum_add_distrib,hW,f,Boulevard.stillA]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hp]; refine Trio.kinds B Q z w' (fun i j =>?_) hq h e a x he ?_
  · unfold w'; split_ifs; exact hf i; exact CouplingShape.reg_const _
  intro i P hP hh l hl hu; rw [hW]; exact hM i P hP hh l hl hu
end YM.LocalLTE.Patch
