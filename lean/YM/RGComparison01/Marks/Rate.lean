import YM.RGComparison01.AuxGeo
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cirrus
/-!
# Polynomial in the stipulated geometrical quantities

 `Rate` from fixed-stage pricing is convenient for the terms using a
 spare power of coupling. E.g. after earning an additional unmarked
 head. Use the *stronger* pricing statement in estimates where giving
 a power would damage the iteration. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {L : Side} {f g : ℝ→ℝ} {v : ℝ}
local notation "T" => fun x:ℝ => Pressure.fiery G x L
lemma Geo.compact (hp : Geo G L f) (h : g=ᶠ[atTop] f) : Geo G L g := by
  obtain ⟨C,k,h,K⟩:=hp; exact ⟨C,k,h,by rwa [eventually_congr (‹g=ᶠ[atTop] f›.mono (fun x hx => by rw [show g x=f x from hx]))]⟩
lemma Geo.small (hp : Geo G L f) (h : ∀ᶠ x in atTop, |g x|≤|f x|) : Geo G L g := by
  obtain ⟨C,k,hc,K⟩:=hp; exact ⟨C,k,hc,(h.and K).mono fun i he=> he.1.trans he.2⟩

/-- Geo after INV-THRESHOLD. Used here for `fiery` (not with a
 new coupling interval). -/
def Fine (G : Gauge) (L : Side) (f : ℝ→ℝ) := Geo G L fun x=> f x*(Pressure.fiery G x L)⁻¹
namespace Fine
lemma dividend (hp : Fine G L f) : Rate G L (-(1/2)) f:= by
  have hz:= (Geo.rate hp|>.mul Rate.flame); rw [zero_add] at hz; refine Rate.congr hz ?_; filter_upwards [Delay.shift_pos G L] with x hx; have hh : 0 < Pressure.fiery G x L:= Work.E09.temp_pos hx
  rw [mul_assoc, inv_mul_cancel₀ hh.ne',mul_one]
lemma slow (h : Fine G L f) : Geo G L f:=by
  have he:= h.dividend.below (by norm_num) 1 zero_lt_one
  refine (Geo.fixed (G:=G) (L:=L) 1).small (he.mono fun i hi=>?_)
  rwa [abs_one]
lemma plus (hf : Fine G L f) (hg : Fine G L g) : Fine G L fun x=> f x+g x := by unfold Fine; simp_rw [add_mul]; exact Geo.joins hf hg
lemma grind_left (hf : Geo G L f) (hg : Fine G L g) : Fine G L fun x=> f x*g x := by unfold Fine; simp_rw [mul_assoc]; exact hf.times hg
lemma grind_right (hf : Fine G L f) (hg : Geo G L g) : Fine G L fun x=> f x*g x := by simp_rw [mul_comm (f _)]; exact grind_left hg hf
lemma higher (hf : Fine G L f) : Fine G L fun x=> |f x| := by
  unfold Fine; apply Geo.compact (Geo.mean hf); filter_upwards [Delay.shift_pos G L] with x hx
  rw [abs_mul, abs_of_pos (inv_pos.mpr (show 0<Pressure.fiery G x L from Work.E09.temp_pos hx))]
lemma flame : Fine G L (T) := by
  apply (Geo.fixed 1).compact; filter_upwards [Delay.shift_pos G L] with x hx
  exact mul_inv_cancel₀ (lt_of_lt_of_le (show 0<Pressure.fiery G x L from Work.E09.temp_pos hx) le_rfl).ne'
lemma inversed (p : ℝ) (h : Fine G L f) : Geo G L (fun x=> (p*Pressure.fiery G x L)⁻¹*f x) := by
  apply Geo.compact (Geo.times (Geo.fixed p⁻¹) h); filter_upwards with x; rw [_root_.mul_inv_rev]; ring
lemma exploded (h : Fine G L f) : Geo G L (fun x=>burst G L x * f x) := by
  have he: Geo G L (fun t=> burst G L t*Pressure.fiery G t L) := by
    refine ((Geo.fixed (Real.sqrt 2)).times Geo.by_delay).compact ?_
    filter_upwards [Delay.shift_pos G L] with x hx
    unfold burst Pressure.fiery Pressure.temp
    rw [Real.sqrt_mul zero_le_two]; unfold Delay.fineMonitor
    ring_nf; field_simp [(Real.sqrt_pos.mpr hx).ne']
    rfl
  refine (he.times h).compact ?_; filter_upwards [Delay.shift_pos G L] with x hx
  field_simp [(show 0<Pressure.fiery G x L from Work.E09.temp_pos hx).ne']
end Fine

lemma Geo.radii : Geo G L (fun x=> (radiusB x:ℝ)) := Geo.basic Lantern.Bolt.size
lemma Geo.tilling : Geo G L (fun x=> (till x:ℝ)) := by
  refine Geo.radii.small (Eventually.of_forall fun x=> ?_); rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast Nat.div_le_self ..
lemma Geo.balling {f : ℝ→ℕ} (hf : Geo G L fun x=> (f x:ℝ)) : Geo G L fun x=> (Animals.ballCost (f x):ℝ) := by unfold Animals.ballCost; push_cast; exact (((hf.joins hf).joins (Geo.fixed 1)).power 4)
end YM.RGComparison01
