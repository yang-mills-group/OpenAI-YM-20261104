import YM.LocalLTE.Units.Grove
import YM.LocalLTE.Units.Forms
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Bridge
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Mover
/-! Use same period when proving further words. Canonical fold, emits in origin/stencil supports. ALL internal choices may use Q. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} (t:Site c) (r:ℕ) (hc:2*(2*r) ≤ c.val)
namespace Fold
local notation "p"=> Slide.cognac hc
open Lattice Slide
abbrev corner:= t-wrap c (Slide.lev r)
local notation "d"=> FrameBox.Fold.corner
def pullV (U:Config G c): Config G c:= Lattice.translate (- d t r) (shape (p) (d t r) U)
lemma homes (z:Site c): Slide.sites (p) (d t r) z∈neighbors r t:= by
  let x:= Slide.stage (p) z; let u:= x- Slide.lev r
  have he : x∈ Slide.crystal (2*r):= stamp hc z
  have hg : u∈Lattice.box r := by apply (translate_crystal ..).2; rwa [show u+ Slide.lev r=x from sub_add_cancel ..]
  apply (neighbors_mem ..).2; rw [show Slide.sites (p) (d t r) z=wrap c u+t from (by change wrap c x + (t-wrap c (Slide.lev r))=_; unfold u; rw [map_sub]; abel)]; exact Slide.sep u t hg
lemma collaborates (U V:Config G c) (h:Agrees (neighbors r t:Set (Four (Per c))) U V):pullV t r hc U=pullV t r hc V:=by unfold pullV; rw [Slide.stable (p) (d t r) (neighbors r t) (homes t r hc) U V h]
lemma selfV (U:Config G c) (hz:2*(r+1)<c.val): Agrees (neighbors r t : Set (Four (Per c))) (pullV t r hc U) U:= by
  refine Slide.readNear t hz ?_; let a:= Slide.lev r
  rintro ⟨i,j⟩ hi hj
  have hq:i+a ∈ Slide.crystal (2*r):= (translate_crystal r _).1 hi; have hm:(i+a+step j)∈crystal (2*r):= by rw [add_right_comm]; exact (translate_crystal r _).1 hj
  have h0 : wrap c (i+a) + d t r = wrap c i+t:= by rw [map_add]; unfold Fold.corner a; abel
  change shape (p) _ U (wrap c i+t + -(d t r),j)=_
  rw [← sub_eq_add_neg,← (eq_sub_of_add_eq h0),vested hc (i+a) hq j hm,h0]; rfl
lemma render (s:ℝ) (U:Config G c) (hp:0 ≤ s) (h:Healthy s (neighbors r t) U): flags s (pullV t r hc U)=∅:= by unfold pullV; rw [← pull_one]; exact Pane.tranquility _ (allFlag _ _ U _ (homes t r hc) s hp h) _ _
-- keep SUN stricter. Since FIN flags, can shrink.
lemma burn (B:BudgetPoint)(U:Config G c)(h:U∈ sunny B):pullV t r hc U∈ sunny B:=by
  have he : ∀ᶠ x:ℝ in 𝓝[<] B.threshold,0≤x ∧ Healthy x (neighbors r t) U:= by
    refine (Eventually.filter_mono nhdsWithin_le_nhds (eventually_ge_nhds B.threshold_pos)).and ((eventually_all.mpr (fun i=>Eventually.filter_mono nhdsWithin_le_nhds (eventually_ge_nhds (h i)))).mono ?_); intro a ha
    apply Finset.disjoint_left.mpr
    intro i _ hx; obtain ⟨y,_,hy⟩:= (flags_spec ..).1 hx; exact hy.not_ge (ha _)
  obtain ⟨y,⟨hp,hP⟩,hy⟩:= (he.and (self_mem_nhdsWithin)).exists; intro i;
  apply lt_of_le_of_lt _ (show y<B.threshold from hy)
  have he:flags y (pullV t r hc U)=∅:=render t r hc y U hp hP
  by_contra! H
  have hz:= (flags_spec y (pullV t r hc U) i.1).mpr ⟨i,WilsonStartup.anchor_visit _,H⟩
  exact notMem_empty _ (he ▸ hz)


local notation "E"=> Directions G c
local notation "A"=> (p)
def digit (i:Bond c):E→L[ℝ] G.Color:=
  if grade (p) i=1 then ContinuousLinearMap.proj (sites (A) (d t r) i.1,i.2) else if grade (p) i= -1 then -(ContinuousLinearMap.proj (sites (A) (d t r) (i.1+step i.2),i.2)) else 0

def trace : E→L[ℝ] E:=ContinuousLinearMap.pi (fun i=>digit t r hc (i.1+ -(d t r),i.2))
lemma invoice (v:E) :‖Fold.trace t r hc v‖≤‖v‖:=by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=>?_); change ‖digit t r hc _ _‖≤_; unfold digit; split
  · exact norm_le_pi_norm v _
  split
  · change ‖-v _‖≤_; rw [norm_neg]; exact norm_le_pi_norm v _
  simp
lemma rehearse (v:E) : pullV t r hc (Grove.soloV v)=Grove.soloV (Fold.trace t r hc v):=by
  funext i; change (shape (p) _ (Grove.soloV v)) _= G.lieExp (digit t r hc _ _)
  unfold Slide.shape digit
  split
  · rfl
  split
  · change (G.lieExp _)⁻¹ = G.lieExp (-v _); rw [Work.F03.exp_neg_color]
  simp
lemma chord_move (a : ℝ)(ha:0≤a)(U:Config G c)(hp:∀ i:Bond c,Grove.fits i t r→G.chord (U i) ≤ a)(i:Bond c): G.chord (pullV t r hc U i)≤ a:= by
  set j:Bond c:=(i.1+ -(d t r),i.2); let o:= d t r; change G.chord (shape (p) o U j)≤a
  unfold Slide.shape; split
  next hh=> exact hp (Slide.sites (p) o j.1,j.2) ⟨homes t r hc _,Slide.here _ _ j.1 j.2 hh ▸ homes t r hc (_+_)⟩
  split
  next hh=> rw [G.chord_inv]; exact hp (Slide.sites (p) o (j.1+step j.2),j.2) ⟨homes t r hc _,(Slide.there (p) o j.1 j.2 hh).symm ▸ homes t r hc j.1⟩
  exact G.chord_one.le.trans ha
end Fold
end YM.LocalLTE.FrameBox
