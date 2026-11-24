import YM.MS.ScaleForest.Entry
import YM.MS.ScaleForest.Joints
import YM.MS.Dial.Slope
/-!
# From the angular graphs to `DOrd` at all separated points

No term-by-term graph match hypotheses with the prescription. Maps into
values of the actual MS_Data cumulant, for generic `Booked` columns. The
calibrated clients / conversion proofs will use these formulas through all
heights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Emit
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric Outlook Vane Land Orbit Local.Physical Tide
open scoped Topology ContDiff
variable {G : Gauge} {I W : Type} [LinearOrder W] {b : Bool} {n p : ℕ} (V:Palette G)

namespace Planted
-- read the actual forest on physical axes
variable (μ:ℝ)
private lemma RenWave (w : ℕ)(L: Hist G b w) (k:ℕ) (t:ℝ)(x:I) : Lift (Parade (renHistory L) w μ t)
    (backing (k-(w:ℂ)) ((L.map (fun i=> asLeaf i.instructions.renorm μ k)).sum) 0 t x) := by
   induction L with
   | nil=> rw [ren_nil,pageZ,backing,List.map_nil,List.sum_nil]; simp only [Pi.zero_apply,← cert,map_zero]; exact Lift.zero
   | cons l L ih=>
      have he:= Rub (l.accepted.after.toll μ t) 0
      rw [ren_cons,List.map_cons,List.sum_cons, page_add, show backing _ (asLeaf l.instructions.renorm μ k+_) 0 t x = backing (k-(w:ℂ)) (asLeaf l.instructions.renorm μ k) 0 t x+ backing (k-(w:ℂ)) ((L.map (fun i=> asLeaf i.instructions.renorm μ k)).sum) 0 t x from (map_add (plower ..) _ _), leafValue k w μ l.instructions.renorm l.accepted.after.toll ]; exact Lift.add he ih

lemma groveSense (I:Type) (μ:ℝ)(V:Palette G): bulkStation (I:=I) V μ = fun n (_:I) t=> Archive 4 (bulkSeries V) n (μ,t) := by
   funext n i t; obtain h:= chosen (n:=0) (Lift.congr (RenWave μ 4 (bulks V n) 0 t i) (Train.prom (panel_sum _) _ t μ));
   change plow (-4) t _ 0= _; norm_num at h; exact congr_fun h 0

lemma groveMark (I:Type) (μ:ℝ)(V:Palette G)(p:Script G) : pinStation (I:=I) V μ p = fun n (_:I) t=> Archive p.1 (atMark V p.2) n (μ,t) := by
   funext n i t; obtain h:= chosen (n:=0) (Lift.congr (RenWave μ _ (marked V p.2 n) p.1 t i) (Train.prom (panel_sum _) _ t μ));
   simp only [sub_self] at h; change backing _ (nominal μ _) 0 t i 0= _; unfold nominal; rw [List.map_map]; exact congr_fun h 0

variable {D: Local.Physical.Deck G} {B: Land.Booked D} (A: Land.MS_Data G B)
   (Q:W→Rake.Label D)

def inducted (R: Land.Booked D) (q:Rake.Label D): Script G:= ⟨ q.h,markVertex R q.h q.item ⟩

variable [TopologicalSpace I] [FirstCountableTopology I] {x:Rake.Position W I}
variable (h:MapGap x)
include h
local notation "frameM"=> (Tide.frameF I μ)
local notation "κ"=> (inducted B ∘ Q)

/-- The native geometry (log UV price on symbolic Glade) and identity after
calculating the one-source forests with the *actual labelled MS optics*.
Comet/leader values used were derived already for these inputs. -/
theorem scoperBody : Vane.DOrd B frameM A Q x (mesur V κ x μ) := by
   obtain H:= recurrence V (inducted B∘Q) x μ h
   have ht:bulkStation (I:=I) V μ= approach frameM A:= by rw [groveSense,reached_bulk V A]; rfl
   have hm(q:Rake.Label D): pinStation (I:=I) V μ (inducted B q)= rowM frameM A q := by rw [groveMark I]; rw [show atMark V (inducted B q).2=marksOn V B q.h q.item from rfl]; simp only [inducted,reached_at V A]; rfl
   rw [ht] at H; simp_rw [Function.comp_apply,hm] at H; exact H
omit [LinearOrder W] [FirstCountableTopology I] in
theorem native_space : Rake.Mesh frameM x := by
   intro i j hQ; obtain ⟨hf,hV,hU⟩:= h i j hQ;
   exact ⟨ by simpa [frameF,Geo.roots] using hV, by simpa [frameF,Geo.roots] using hU⟩

theorem quoteVision (i:I) : priceMap V μ κ x i= Dial.book A Q μ (Dial.pointI x i):= by
   obtain hv:= scoperBody V μ A Q h; obtain hT:=native_space μ h
   funext S n; rw [ ← Dial.Point_t A Q μ hT hv ];
   unfold Fleet.toZ Vane.blade mesur; rw [throughput μ _ (atlas_hired V κ x h S n)]; rfl

-- on every separated frame
omit h
omit [LinearOrder W] in
lemma gathering {x:W→QP} (h: Injective x): MapGap (I:=Unit) (fun i _=> x i) := by
   intro i j hp; obtain he : 0 < ‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hp)); refine ⟨ continuous_const,⟨ _,he,?_⟩,⟨_,he,?_⟩⟩ <;> exact fun _ => le_rfl

lemma pointCampaign {x:W→QP} (hp:Injective x) : priceBook V μ κ x= Dial.book A Q μ x := quoteVision V μ A Q (gathering hp) ()
end Planted
end YM.MS.ScaleForest
