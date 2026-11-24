import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Burst
/-! # The pointwise statements for iterated position operations in (G.9).
    First, second etc, in the same r units. Preserve exact ordering under the expansions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type*} {F:Filter I}
-- always r-length. Off-conf fderiv not used.
def dots : List (Fin n × Axis) → (Points n→ℂ) → Points n→ℂ
  | [],u=>u
  | (i,b)::l,u=> dots l (Points.gradient i b u)
variable (k:Fin n × Axis)(u:Points n→ℂ)
local notation "ϕ" => conf n
set_option quotPrecheck false
local notation "dᶠ" => Points.gradient k.1 k.2
lemma points_cons (l:List (Fin n × Axis))(u:Points n→ℂ) : dots (k::l) u=dots l (dᶠ u) := rfl
variable (l : List (Fin n×Axis)) {x:Points n} (hx:x∈conf n)
lemma diff (h:ContDiffOn ℝ ∞ u ϕ) : ContDiffOn ℝ ∞ (dots l u) ϕ := by
  induction l generalizing u with | nil=>exact h| cons a l ih=>rw [points_cons]; exact ih _ (dcost h a.1 a.2)
include hx
lemma dots_on {u f: Points n→ℂ} (h:EqOn u f ϕ) : dots l u x=dots l f x := by
  induction l generalizing u f x with
  | nil=>exact h hx
  | cons a l ih=> simp_rw [points_cons]; apply ih hx; intro x hx; exact Analysis.GermD _ (Eventually.mono ((conf_open _).mem_nhds hx) fun x hx=>h hx )

lemma dsums (B: Finset I) (f:I→Points n→ℂ)(h:∀ i∈B,ContDiffOn ℝ ∞ (f i) ϕ) :
    dots l (fun x=>∑ i∈B,f i x) x = ∑ i∈B,dots l (f i) x := by
  induction l generalizing x f with
  | nil=>rfl
  | cons a l ih =>
    rw [points_cons]; have he i: dots (a::l) (f i)=dots l (Points.gradient a.1 a.2 (f i)) := points_cons ..; simp_rw [he]
    refine Eq.trans (dots_on l hx ?_) (ih hx (fun i=>Points.gradient a.1 a.2 (f i)) (fun i hi=> dcost (h i hi) a.1 a.2))
    intro x hx; unfold Points.gradient Analysis.D; rw [fderiv_fun_sum]; · rw [_root_.sum_apply]
    exact fun j hj=>( (h j hj|>.contDiffAt ((conf_open _).mem_nhds hx))).differentiableAt (by simp)
lemma dconst {u:Points n→ℂ} (h:ContDiffOn ℝ ∞ u ϕ) (a:ℂ) : dots l (fun x=>a*u x) x = a*dots l u x := by
  induction l generalizing x u with
  | nil=> rfl
  | cons j l ih=> rw [points_cons,points_cons]; refine Eq.trans (dots_on l hx ?_) (ih hx (dcost h j.1 j.2)); intro x hx; unfold Points.gradient Analysis.D; rw [fderiv_const_mul ((h.contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)) a]; rfl
omit hx

variable {G:Gauge} {N : WilsonPrescription G} {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S) (hJ:Leading U J)
    {A : ∀ d:ℕ, ℝ→Change G d} (P:Realized J Y N A (Paper.meter U J N.criterion))
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial)
    (h : Shop U J N) (hp: normal U J N.store)
    (a:Tags G d n) (v : Viewers U) {r:ℝ} (hr:0<r)
local notation "𝕄" => physicalY U Y
local notation "FN" => storyV N
variable (Q:Spare N (d+1)) (p:ℕ)
include hr hx
lemma banked (H0:heights U Y r (d+1)) : dots (k::l) (𝕄 v a r) x =
    ∑ i: Toon G (d+1), coord i (upgrade U Y d r k.2 (a k.1)) * dots l (𝕄 v (roster a k.1 i) r) x := by
  rw [points_cons]; have hi u : ContDiffOn ℝ ∞ (𝕄 v u r) ϕ := fun x hx=> (regular_at U Y v hr hx (l:=d+1) u).contDiffWithinAt
  refine Eq.trans (dots_on l hx (fun _ hz=> directional U Y k.2 a k.1 hz v hr H0)) ?_
  rw [dsums l hx]; · exact Finset.sum_congr rfl fun i _=> dconst l hx (hi _) _
  exact fun i _=> contDiffOn_const.mul (hi _)
omit hr
include H h hp hJ P
def indexed (N: WilsonPrescription G) (k:List (Fin n×Axis)) (a:Tags G d n) (x:Points n) := PowerSeries.mk fun i=> dots k (fun x=> coeff i (storyV N a x)) x
lemma compounded : indexed N (k::l) a x = ∑ i:Toon G (d+1), sizeIt N Q (a k.1) k.2 i * indexed N l (roster a k.1 i) x := by
  ext1 j; rw [indexed, coeff_mk,map_sum,points_cons]; let V (s:List (Fin n×Axis))(a:Tags G (d+1) n)(u:ℕ): coeff u (indexed N s a x)=dots s (fun x=>coeff u (FN a x)) x := coeff_mk ..; simp_rw [coeff_mul, V]
  let Qz i:=sizeIt N Q (a k.1) k.2 i; let W i:=storyV N (roster a k.1 i)
  let f (i:Toon G (d+1))(u:ℕ×ℕ)(x:Points n):= coeff u.1 (Qz i)*coeff u.2 (W i x); have X i u : ContDiffOn ℝ ∞ (fun x=> coeff u (W i x)) ϕ:= PT_cost N M H (roster a k.1 i) u
  have E i u : ContDiffOn ℝ ∞ (f i u) ϕ:= contDiffOn_const.mul (X i u.2)
  let s:=Finset.HasAntidiagonal.antidiagonal j
  let F (x:Points n) := ∑ i:Toon G (d+1),∑u∈s,f i u x
  refine Eq.trans (dots_on l hx (f:=F) (fun x hx=>?_)) ?_
  · rw [derivative_eq U J Y N hJ P M H h hp Q k.2 a k.1 hx,flare]; simp_rw [map_sum,coeff_mul]; rfl
  unfold F; rw [dsums l hx _ _ (fun i _=> ContDiffOn.sum (fun u _=> E i u) )]
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [dsums l hx _ _ (fun u _=>E i u)]
  exact Finset.sum_congr rfl fun u _=>dconst l hx (X i u.2) _
end YM.FVA2.GradedFar259.Sparks
