import YM.MS.ScaleForest.Recorder
/-!
# Moment sums and normalization

The graph prescription here is constructed WITH the same normalization as
in the files, i.e., vacuum components have been removed. No unit factor per
diagram. For moments the sector recursion is literally the connected graph
sum followed by EXPONENTIAL (or do ordered partitions of named occurrences;
source sectors include the vacuum normalization). For the explicit
vacuum-denominator check see `RoomNumber`. For clarity check formulas
for every moment here. This fixes also the empty-list conventions and
one-point cumulants: in particular we don't remove contractions from a
single pin to itself. Marker with no momentum legs still counts as ONE pin.
Vacant/unit term at a single location can use `b=false`, and if inside a
family with multiple locations `b=true`; b tag in Planted tracks
number of locations, not momentum or marker grade.

By construction this uses normalized exponential of exactly the connected,
nonvacuum series (for empty pin SET the connected part is zero). Wouldn't
compute a raw finite correlator: all external steps of the theorem to
report use the same coupling/field matches and the prescribed moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Emit
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric Outlook Vane Land Orbit Local.Physical Tide
open Puff Puff.Mom Actors
open scoped Topology ContDiff
namespace Planted
variable {W I:Type}[LinearOrder W]{G:Gauge}

/-- Ordered by first extracted component. The convention later divides by k!. -/
def joinsP (F:Finset W→ T ℂ) : ℕ→ Finset W→ T ℂ
 | 0, s,i=> if s=∅ ∧ i=0 then 1 else 0
 | k+1,s,i=> ∑ l∈s.powerset,∑ j∈ Finset.antidiagonal i,F l j.1 * joinsP F k (s\l) j.2

def byPartition (F:Finset W→ T ℂ) : Finset W→ T ℂ:= fun s j=> ∑ k∈ Finset.range (s.card+1), (Nat.factorial k : ℂ)⁻¹ * joinsP F k s j

lemma countParts (F: Finset W→ T ℂ) (k:ℕ): joinsP F k= (Trunk.stack (SplitP.marked W)).power F k:= by
   classical
   induction k with
   | zero=>
      funext s n; change _=(SplitP.refineV (SplitP.marked W) ((SplitP.nat).refineV (1:ℂ)) s) n
      unfold SplitP.refineV; simp only [SplitP.marked,SplitP.nat]; split_ifs with H
      all_goals simp [joinsP, *]
   | succ k ih=> funext s i; change _=(∑ j∈SplitP.subs s, Trunk.core (F j.1) ((Trunk.stack (SplitP.marked W)).power F k j.2) ) i
                 rw [Finset.sum_apply, SplitP.sumS (fun p q=> Trunk.core (F p) ((Trunk.stack (SplitP.marked W)).power F k q) i),← ih]; rfl -- binder
lemma part_eq (F: Finset W→ T ℂ): byPartition F= bouquet F := by
   funext s j; unfold byPartition bouquet Puff.Actors.Cheer; simp_rw [cheers,wages,countParts]; simp_rw [Finset.sum_apply,Pi.smul_apply]; rfl

-- empty chart bills — record before and after regulator specialization, no implicit pin at ∅
variable (V:Palette G)(K:W→Script G)(μ:ℝ) (x:Rake.Position W I)

def staying (s:ℝ)(z:ℂ)(i:I) : Finset W→ T ℂ:= fun p j=> fundraiser μ (atlas V K x p j).2 z s i 0 []
def stayed (s:ℝ)(i:I) : Finset W→ T ℂ:= fun p j=> costTable μ (atlas V K x p j).2 i s 0 []
lemma unused (i:I) : (∀ s z, staying V K μ x s z i ∅=0) ∧ (∀ s,stayed V K μ x s i ∅=0) ∧ priceMap V μ K x i ∅=0:= by
   have hh(n:ℕ): atlas V K x ∅ n=⟨ false, []⟩:= by unfold atlas tray; rw [if_neg (by simp), dif_neg (by simp)];
   have he : ∀ (s:ℝ) (z:ℂ) (p: I), staying V K μ x s z p ∅=0:= by intro a b c; funext n; unfold staying; rw [hh]; simp [fundraiser, backing, ← cert]
   have hm : ∀ s:ℝ,stayed V K μ x s i ∅=0:= by
       intro s; funext n; unfold stayed costTable; rw [show (fun z=> fundraiser μ (atlas V K x ∅ n).2 z s i) = 0 from ?_]; simp [ruby0]
       funext z; rw [hh]; simp [fundraiser,backing, ← cert ];
   refine ⟨ fun a b=> he a b i, hm,funext fun n=>?_⟩;
   have hu (s:ℝ): costTable μ (atlas V K x ∅ n).2 i s 0 []=0:= congr_fun (hm s) n
   unfold priceMap stipend; simp_rw [hu]; exact tendsto_const_nhds.limUnder_eq
lemma enough_parts (F: Finset W→ T ℂ)(h:F ∅=0)(s:Finset W)(n:ℕ)(hv:s.card<n): joinsP F n s=0 := by rw [countParts]; exact Actors.pole Trunk (SplitP.marked W) F h hv

variable [TopologicalSpace I][FirstCountableTopology I]

-- no product changes order of UV specialization or IR projection

def income (Q:Rake.Position W I)(i:I) := byPartition (priceMap V μ K Q i)
lemma IncomeLaw (h:MapGap x)(s:Finset W)(j:ℕ)(i:I) :
     (∀ r:ℝ,Tendsto (fun z=> byPartition (staying V K μ x r z i) s j) dotty (𝓝 (byPartition (stayed V K μ x r i) s j))) ∧
     Tendsto (fun t:ℝ=> byPartition (stayed V K μ x t i) s j) atTop (𝓝 (income V K μ x i s j)) := by
   simp_rw [income,part_eq]; constructor; · intro t; exact Accord.select (f:=fun z=> staying V K μ x t z i) (fun r n=> salary _ (atlas V K x r n).2 (atlas_hired V K x h r n) t i 0 []) s j
   exact Accord.select (f:=fun t=> stayed V K μ x t i) (fun r n=> (authorized_IR _ (atlas V K x r n).2 (atlas_hired V K x h r n) i).2) s j
variable {B:Deck G}{O:Land.Booked B} (A:MS_Data G O)(F: W→ Rake.Label B)
lemma commission (h:MapGap x)(i:I) : income V (inducted O ∘ F) μ x i = Dial.tour A F μ (Dial.pointI x i):= by unfold Dial.tour income; rw [part_eq, quoteVision V μ A F h]
lemma point_income {x:W→QP}(h:Injective x): byPartition (priceBook V μ (inducted O ∘ F) x)= Dial.tour A F μ x := commission V μ (fun i _=>x i) A F (gathering h) ()
end Planted
end YM.MS.ScaleForest
