import YM.GradedFar.Round.Deck
import YM.GradedFar.Round.Crew

/-!
# Rolling geometry for the (G.9) receipts (relative positions, including centers)
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t p : ℕ} {I J:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

lemma enlarge_knob {K F : Set (Points n)}(hK:IsCompact K)(hf:IsOpen F)(hx:K⊆F) :
    ∃ (X:Set (Points n)), IsCompact X ∧ X⊆F ∧ K⊆X ∧ ∃ c:ℝ,0<c ∧ ∀ x∈K,Metric.closedBall x c⊆ X := by
   obtain ⟨c,hc,h⟩:= hK.exists_cthickening_subset_open hf hx
   let X:= Metric.cthickening c K
   exact ⟨X,hK.cthickening, h, Metric.self_subset_cthickening K,c,hc,fun i hi=> Metric.closedBall_subset_cthickening hi c⟩

/-- `May`: precision guarantee on the rounding supplied by C's geometry hypothesis.
 Even Far rounding is in `r` units. This is on Euclidean shape coordinates in finite arity
 in the two zones, uniform in same x,y. -/
structure May (G:Gauge)(Q:Set Continuation.Window)(I:Type) (x:I→Points n) (y:I→Points m)
    (Z:Continuation.Window→I→Points n)(S:Continuation.Window→I→Points m)(A:ℕ) : Prop where
   fields : Terms (windows Q) (fun (w:Continuation.Window)=>gYM G w.len^A) (fun w i=> Z w i-x i)
   exterior : Terms (windows Q) (fun (w:Continuation.Window)=>gYM G w.len^A)
       (fun (w:Continuation.Window) i=> w.Stretch • (S w i-y i))

-- paths (explicitly continuous geometry even off mesh compared)
def along (w:Continuation.Window)(x:Points n)(y:Points m):= forest x (w.Stretch • y)
lemma to_along {X : Set (Points n)} {S:Set (Points m)}(v:XSet X S)(w:Continuation.Window) : flute v w.sep=along w v.1 v.2:= by
   unfold along flute; rw [wide_here]
section
variable {Q:Set Continuation.Window} {x:I→ Points n}{y:I→ Points m}{Z:Continuation.Window→I→Points n}{S: Continuation.Window→I→Points m}
include simple
lemma nearby {C D:ℝ} (hC:0<C)(hD:0<D) {A:ℕ}(hA:0<A)(h:May G Q I x y Z S A) :
    ∀ᶠ (w:Continuation.Window) in windows Q, ∀ i,
       dist (Z w i) (x i)≤ C ∧ dist (S w i) (y i)≤ D := by
   obtain ⟨c,hc,h⟩:= h.fields.price; obtain ⟨d,hd,h'⟩:= ‹May G Q I x y Z S A›.exterior.price
   have hv (d:ℝ): Tendsto (fun (w:Continuation.Window)=> d*g w.len^A) (windows Q) (𝓝 0):= by simpa only [zero_pow hA.ne',mul_zero, comp_apply] using (((shrink simple).comp (windows_short Q)).pow A).const_mul d
   filter_upwards [h,h',(windows_separation Q).eventually_ge_atTop 0,(windows_short Q).eventually (positive_g simple),(hv c).eventually_lt_const hC,(hv d).eventually_lt_const hD] with w h h' hk hg hx hy i
   have he:=h' i; have hh:= h i; have hu:1≤Window.Stretch w:= Real.one_le_exp hk
   rw [Real.norm_of_nonneg (pow_nonneg hg.le _)] at he hh; rw [norm_smul,Real.norm_of_nonneg (zero_le_one.trans hu)] at he
   rw [dist_eq_norm,dist_eq_norm]; exact ⟨hh.trans hx.le, (le_trans (le_mul_of_one_le_left (norm_nonneg _) hu) he).trans hy.le⟩
omit simple in
lemma path_location (x x':Points n)(y y':Points m)(w:Continuation.Window)(C:Set (Points n))(S:Set (Points m)) (hc:segment ℝ x x'⊆ C)(hs:segment ℝ y y'⊆ S) :
   ∀ l∈segment ℝ (along w x y) (along w x' y'), ∃ i∈C,∃ j∈S,l=along w i j := by
   rintro l ⟨a,b,ha,hb,h,rfl⟩
   refine ⟨a•x+b•x',hc ⟨a,b,ha,hb,h,rfl⟩, a•y+b•y',hs ⟨a,b,ha,hb,h,rfl⟩,?_⟩
   ext1 i; induction i using Fin.addCases with
   | left i=> simp [along]
   | right i=> simp [along,smul_add]; congr 1 <;> exact smul_comm ..

set_option linter.unusedSectionVars false in
lemma rounding_distance {A:ℕ}(h:May G Q I x y Z S A) : Terms (windows Q) (fun (w:Continuation.Window)=>gYM G w.len^A)
    (fun (w:Continuation.Window) i => along w (Z w i) (S w i) - along w (x i) (y i)) := by
   let L : Points n × Points m →L[ℝ] Points (n+m) := { DerivD.tribe (n:=n) (m:=m) with cont := O.Enh.continual (n:=n) (m:=m) continuous_fst continuous_snd }
   obtain ⟨C,hC,hL⟩:= h.fields.price; obtain ⟨D,hD,hR⟩:= h.exterior.price
   apply Terms.of_be; refine ⟨‖L‖*(C+D),?_⟩; filter_upwards [hL,hR] with w hL hR i
   let v:=Window.Stretch w; rw [show along w (Z w i) (S w i) - along w (x i) (y i)= L (Z w i - x i, v • (S w i-y i)) from ?eq]
   case eq=> exact (show L (Z w i,v• S w i) - L (x i,v•y i)=_ by rw [← map_sub, smul_sub];rfl)
   apply (L.le_opNorm _).trans
   rw [Prod.norm_def, mul_assoc,add_mul]; refine mul_le_mul_of_nonneg_left (max_le (?_) (?_)) (norm_nonneg _)
   · apply (hL i).trans; exact le_add_of_nonneg_right (by positivity)
   exact (hR i).trans (le_add_of_nonneg_left (by positivity))
end
end
end YM.FVA2.GradedFar.Physical.Round
