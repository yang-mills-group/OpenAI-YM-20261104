import YM.Integration.WilsonMaxwellThermometerFirstDetector
import YM.Integration.WilsonSeparatedOriginalThermometerCells

/-! A common integral translate of the three independently rounded child
addresses places the actual first-order panel in the finite detector's box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerShiftedPanel
open Function Set Filter Finset Metric Lattice Extraction MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector
open scoped Topology BigOperators Classical

def shift (m : Mesh) : Cover := fun _ => ((m.p.side.val / 8 + 1 : ℕ) : ℤ)
def center (m : Mesh) : Four ℝ := fun a=>m.spacing*(shift m a : ℝ)
def translated (m : Mesh) (v : pack 3) : Sample 3 :=
  ⟨m,fun i=>v i+shift m,center m⟩

theorem accepted : ∀ᶠ m in Front, center m∈m.Box := by
  filter_upwards [Cirrus.frontier.horizon.eventually_ge_atTop (8:ℝ)] with m size
  change 8 ≤ (m.p.side.val:ℝ) at size
  have big : 8 ≤ m.p.side.val := by exact_mod_cast size
  have l : m.p.side.val≤8*(m.p.side.val/8+1) := by omega
  have u : 4*(m.p.side.val/8+1) ≤ m.p.side.val := by omega
  have lo : (m.p.side.val:ℝ)/8≤((m.p.side.val/8+1:ℕ):ℝ) := by
    have e : (m.p.side.val:ℝ)≤8*((m.p.side.val/8+1:ℕ):ℝ) := by exact_mod_cast l
    linarith
  have hi : ((m.p.side.val/8+1:ℕ):ℝ)≤(m.p.side.val:ℝ)/4 := by
    have e : 4*((m.p.side.val/8+1:ℕ):ℝ)≤(m.p.side.val:ℝ) := by exact_mod_cast u
    linarith
  refine ⟨fun _=>?_,fun _=>?_⟩
  · simpa only [Mesh.size,center,shift,Int.cast_natCast,mul_div_assoc] using
      mul_le_mul_of_nonneg_left lo m.positive.le
  · simpa only [Mesh.size,center,shift,Int.cast_natCast,mul_div_assoc] using
      mul_le_mul_of_nonneg_left hi m.positive.le

theorem location (m : Mesh) (v : pack 3) :
    familiar (translated m v)=Extraction.tag m.spacing v := by
  ext i a
  change m.spacing*((v i a+shift m a:ℤ):ℝ)-
    m.spacing*(shift m a:ℝ) = m.spacing*(v i a:ℝ)
  push_cast
  ring

def cell (m : Mesh) (x : Points 3) : m.Tuple (n:=3) :=
  wrap m.p.side ∘ address m.spacing x

theorem measurable_cell (m : Mesh) : Measurable (cell m) := by
  have h : Measurable (address m.spacing : Points 3→pack 3) := by
    apply measurable_to_countable
    intro a
    exact measurable_segment m.positive (address m.spacing a)
  exact (measurable_of_countable (fun a : pack 3=>wrap m.p.side ∘ a)).comp h

variable {G : Gauge} (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)

def atSites (m : Mesh) (o : m.Tuple (n:=3)) : Point G 6 3 :=
  sampled W (V:=V) (translated m (Mesh.back m o))

theorem same_sites (m : Mesh) (v w : pack 3) (same : wrap m.p.side ∘ v=wrap m.p.side ∘ w) :
    sampled W (V:=V) (translated m v)=sampled W (V:=V) (translated m w) := by
  have addresses : chartV (translated m v) = chartV (translated m w) := by
    funext i
    have h := congrFun same i
    change wrap m.p.side (v i+shift m) = wrap m.p.side (w i+shift m)
    simpa only [map_add,Function.comp_apply] using congrArg (· +wrap m.p.side (shift m)) h
  have filed (e : ℕ) : cooked W V 6 (translated m v) e = cooked W V 6 (translated m w) e := by
    unfold cooked live
    simp only [addresses]
    rfl
  rw [sampled,sampled,filed 0,filed 1]

theorem restore (m : Mesh) (x : Points 3) : atSites W (V:=V) m (cell m x)=
    sampled W (V:=V) (translated m (address m.spacing x)) := by
  apply same_sites
  funext i
  exact wrap_lift _

/-- A single threshold controls every placement in the actual compact Rose support. -/
theorem nearby (p : Tags G 6 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ m in Front, ∀ x∈tsupport (Rose.test K), ∀ v : pack 3,
      dist (Extraction.tag m.spacing v) x≤24*m.spacing →
      dist (sampled W (V:=V) (translated m v) p) (continuum W (V:=V) x p) ≤ ε := by
  let X := tsupport (Rose.test K)
  have stored : IsCompact X := (Rose.test K).hasCompactSupport
  have valid : X ⊆ conf 3 := (Rose.test K).tsupport_subset
  have h := sensed W (V:=V) p
  choose radius positive fee using fun x : X => sensesU h x.val (valid x.property) (ε/2) (half_pos he)
  let ballX (x : X) := ball x.val (radius x/2)
  obtain ⟨u,cover⟩ := stored.elim_finite_subcover ballX (fun _=>isOpen_ball)
    (fun x hx=>mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (half_pos (positive _))⟩)
  have shrink (k : X) : ∀ᶠ m in Front,(24:ℝ)*m.spacing<radius k/2 := by
    have t := frontier.endpt.const_mul (24:ℝ)
    rw [mul_zero] at t
    exact t.eventually (gt_mem_nhds (half_pos (positive k)))
  filter_upwards [accepted,(eventually_all_finset u).mpr (fun k _=>(fee k).and (shrink k))] with m admit budget x hx v good
  obtain ⟨k,hxk⟩ := mem_iUnion.mp (cover hx)
  obtain ⟨mem,inside⟩ := mem_iUnion.mp hxk
  have hk := budget k mem
  have close : dist x k.val < radius k/2 := inside
  refine (dist_triangle _ (continuum W (V:=V) k.val p) _).trans ?_
  apply le_trans (add_le_add ?_ ?_) ((add_halves ε).le)
  · apply le_of_lt (hk.1 _ _ admit ?_)
    change dist (familiar (translated m v)) k.val < radius k
    rw [location]
    exact (dist_triangle _ x _).trans_lt (by linarith [good,close,hk.2])
  · rw [dist_comm]
    exact senses_price h k.val (radius k) (positive k) _ (fee k) x (valid hx) (close.trans (half_lt_self (positive k)))

theorem placed (p : Tags G 6 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ m in Front, ∀ x∈tsupport (Rose.test K),
      dist (atSites W (V:=V) m (cell m x) p) (continuum W (V:=V) x p) ≤ ε := by
  filter_upwards [nearby W K p he] with m ready x hx
  rw [restore W]
  apply ready x hx
  exact (Extraction.approximate m.positive x).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (4*3:ℝ)≤24) m.positive.le)

end YM.Integration.WilsonMaxwellThermometerShiftedPanel
