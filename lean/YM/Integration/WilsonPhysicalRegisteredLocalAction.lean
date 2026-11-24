import YM.Integration.WilsonAxialWindow
import YM.MSbar.Sat.Probe
import YM.PertExtension.BareChart
import YM.Next.RANK.Determinant
import YM.OPE.Therm.Bath

/-! The finite local axial chart in a Wilson conditional. Boundary links stay in
the action. The coarse endpoints of a gauge change transform along with the fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalRegisteredLocalAction
open Lattice RG Wilson MeasureTheory Set Metric PertExtension MSbar.Heath OPE.Therm
open scoped Classical Topology
variable {G : Gauge} {n : Side}

def change (B : Finset (Site n)) (z : Site n → G.El) : Site n → G.El :=
  (B : Set (Site n)).mulIndicator z

def window (B : Finset (Site n)) (E : Finset (Edge (Site n))) (U : Config G n) (b : ℝ) :
    Set (Site n → G.El) := {z | ∀e∈E, G.chord (gauge (change B z) U e) < b}

abbrev colors (G : Gauge) (n : Side) := Measure.pi (fun _ : Site n => G.probHaar)

theorem fixed (B : Finset (Site n)) (z : Site n → G.El) (U : Config G n) (e : Edge (Site n))
    (a : e.1 ∉ B) (b : e.1 + step e.2 ∉ B) : gauge (change B z) U e = U e := by
  simp [Lattice.gauge,change,a,b]

private theorem open_window (B : Finset (Site n)) (E : Finset (Edge (Site n))) (U : Config G n) (b : ℝ) :
    IsOpen (window B E U b) := by
  have cont (x : Site n) : Continuous (fun z : Site n → G.El => change B z x) := by
    by_cases h : x∈B
    · simpa only [change,Set.mulIndicator_of_mem h] using (continuous_apply x : Continuous (fun z : Site n → G.El => z x))
    · simpa only [change,Set.mulIndicator_of_notMem h] using (continuous_const : Continuous (fun _ : Site n → G.El => (1:G.El)))
  have field (e : Edge (Site n)) : Continuous (fun z : Site n → G.El => gauge (change B z) U e) :=
    ((cont e.1).mul continuous_const).mul (cont _).inv
  rw [show window B E U b = ⋂e∈E, {z | G.chord (Lattice.gauge (change B z) U e)<b} by ext z; simp [window]]
  exact isOpen_biInter_finset (fun e _ => isOpen_lt (G.continuous_chord.comp (field e)) continuous_const)

/-- A cold no-wrap plaquette box gives strictly positive Haar mass to local gauge
colours putting every listed link in the literal exponential chamber. -/
theorem admitted (J : Voice G) (clear : Clear G J) (o : Site n) (d : ℕ)
    (fit : 2*d < n.val) (B : Finset (Site n)) (E : Finset (Edge (Site n)))
    (ends : ∀e∈E, e.1∈B ∧ e.1+step e.2∈B ∧ separation o e.1<d)
    (U : Config G n) {t b r : ℝ} (nonneg : 0≤t) (cold : U∈House.chilly (WilsonAxialWindow.cells o d) t)
    (room : 4*(d:ℝ)*Fintype.card PlaqAxes*t < b) (near : b ≤ J.δ) (radius : J.C*b ≤ r) :
    0<(colors G n).real (window B E U b) ∧ ∀z∈window B E U b,
      (fun e : ↥E => gauge (change B z) U e.val) ∈ Chart.chamber G (↥E) r := by
  let z := WilsonAxialWindow.frame 1 o U
  have witness : z∈window B E U b := by
    intro e he
    obtain ⟨a,b,h⟩ := ends e he
    have eq : gauge (change B z) U e = gauge z U e := by simp [change,Lattice.gauge,a,b]
    rw [eq]
    exact (WilsonAxialWindow.bound 1 o U d fit e h nonneg cold).trans_lt room
  constructor
  · have positive := (open_window B E U b).measure_pos (Measure.pi fun _ : Site n=>G.probHaar) ⟨z,witness⟩
    exact ENNReal.toReal_pos positive.ne' (measure_ne_top _ _)
  · intro g inside e _
    let v := gauge (change B g) U e.val
    have hv : G.chord v<b := inside e.val e.property
    have read := clear.near v (hv.le.trans near)
    refine ⟨J.decode v,?_,read.2.1⟩
    rw [mem_ball_zero_iff]
    exact read.2.2.trans_lt ((mul_lt_mul_of_pos_left hv (zero_lt_one.trans_le clear.cost)).trans_le radius)

def weight (A : History G) (N p m : ℕ) (U : Config G (A.S.side (m+1) p)) (V : Config G (A.S.side m p)) : ℝ :=
  (A.rep N p (m+1)).eval U * (A.levels.clock.op m p).density (A.β N p (m+1)) U V /
    (A.rep N p m).eval V

theorem covariant (A : History G) (selected : A.Selected) {N p m : ℕ} (active : m<N)
    (z : Site (A.S.side (m+1) p) → G.El) (U : Config G (A.S.side (m+1) p)) (V : Config G (A.S.side m p)) :
    weight A N p m (gauge z U) (gauge (z ∘ (A.levels.clock.op m p).ratio.embed) V) = weight A N p m U V := by
  unfold weight
  rw [Next.Rank.gauge_eval (selected.represents N p (m+1) active).good,
    (A.levels.blocks m p).gauge,Next.Rank.gauge_eval (selected.represents N p m active.le).good]

/-- The same signed conditional integrand at any held lower field, averaged
over the local chart colours and divided by their actual positive mass. -/
theorem original (A : History G) (selected : A.Selected) {N p m : ℕ} (active : m<N)
    (B : Finset (Site (A.S.side (m+1) p))) (E : Finset (Edge (Site (A.S.side (m+1) p))))
    (U : Config G (A.S.side (m+1) p)) (V : Config G (A.S.side m p)) {b : ℝ}
    (positive : 0<(colors G _).real (window B E U b)) (F : Config G (A.S.side (m+1) p)→ℂ) (inv : GaugeInvariant F) :
    (∫z in window B E U b, weight A N p m (gauge (change B z) U)
        (gauge (change B z ∘ (A.levels.clock.op m p).ratio.embed) V) • F (gauge (change B z) U)
        ∂colors G _) / (((colors G _).real (window B E U b):ℝ):ℂ) = weight A N p m U V • F U := by
  have same (z : Site (A.S.side (m+1) p) → G.El) :
      weight A N p m (gauge (change B z) U) (gauge (change B z ∘ (A.levels.clock.op m p).ratio.embed) V) • F (gauge (change B z) U) = weight A N p m U V • F U := by
    rw [covariant A selected active,inv (change B z) U]
  simp_rw [same]
  rw [setIntegral_const,Complex.real_smul]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr positive.ne')

end YM.Integration.WilsonPhysicalRegisteredLocalAction
