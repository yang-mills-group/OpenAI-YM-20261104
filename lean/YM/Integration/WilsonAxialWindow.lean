import YM.Planned.PRIMARY_INTEGRAL_295.Racks
import YM.OPE.Therm.Rite

/-! The actual coordinate-tree gauge and its local Wilson moments on an embedded periodic box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAxialWindow

open Function Filter MeasureTheory Lattice Wilson RG Axial Work.E08 OPE.Therm
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side}

def frame (k : Lattice.Order) (o : Site n) (U : Config G n) (y : Site n) : G.El :=
  traveller (allAxes k) (expandAt o U) 0 (lift (y-o))

def cells (o : Site n) (r : ℕ) : Finset (Face (Per n)) :=
  ((box r).image fun z => wrap n z+o) ×ˢ (Finset.univ : Finset PlaqAxes)

theorem cell (o : Site n) (r : ℕ) {z : Cover} (hz : z ∈ box r) (p : PlaqAxes) :
    (wrap n z+o,p) ∈ cells o r :=
  Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_univ _⟩

theorem nonempty (o : Site n) (r : ℕ) : (cells o r).Nonempty :=
  ⟨_,cell o r (center_box r) ⟨(0,1),by decide⟩⟩

theorem count (o : Site n) (r : ℕ) : (cells o r).card ≤ (r+r+1)^4*Fintype.card PlaqAxes := by
  unfold cells
  rw [Finset.card_product,Finset.card_univ,← Corona.box_size]
  exact Nat.mul_le_mul_right _ Finset.card_image_le

theorem pull (k : Lattice.Order) (o : Site n) (U : Config G n) (r : ℕ) (hn : 2*r < n.val)
    (x : Cover) (i : Axis) (hx : x ∈ box r) (hxi : x+step i ∈ box r) :
    Lattice.gauge (frame k o U) U (wrap n x+o,i) =
      Lattice.gauge (traveller (allAxes k) (expandAt o U) 0) (expandAt o U) (x,i) := by
  have h (z : Cover) (hz : z ∈ box r) : frame k o U (wrap n z+o) =
      traveller (allAxes k) (expandAt o U) 0 z := by
    unfold frame
    rw [add_sub_cancel_right,Planned.PrimaryIntegral295.Racks.peel hn _ hz]
  change expandAt o (Lattice.gauge (frame k o U) U) (x,i) = _
  rw [expandAt_gauge]
  simp only [Lattice.gauge,h x hx,h (x+step i) hxi]

theorem expanded (o : Site n) (U : Config G n) (x : Cover) (p : PlaqAxes) :
    faceValue (expandAt o U) (x,p) = faceValue U (wrap n x+o,p) :=
  Lattice.travel_at o U x (square p.val.1 p.val.2)

private theorem next_box (x : Cover) (i : Axis) (d r : ℕ) (hx : x∈box d) (he : d<r) :
    x+step i ∈ box r := by
  obtain ⟨hl,hu⟩ := box_test.mp hx
  rw [box_test]
  constructor <;> intro a <;> simp only [Pi.add_apply,step_apply] <;>
    split <;> have := hl a <;> have := hu a <;> omega

theorem bound (k : Lattice.Order) (o : Site n) (U : Config G n) (r : ℕ) (hn : 2*r < n.val)
    (e : Edge (Site n)) (he : separation o e.1 < r) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ z ∈ cells o r, G.chord (faceValue U z) ≤ t) :
    G.chord (Lattice.gauge (frame k o U) U e) ≤ (4*(r:ℝ)*Fintype.card PlaqAxes)*t := by
  let x := lift (e.1-o)
  have hx : x ∈ box (separation o e.1) := lift_mem_box le_rfl
  have hv := next_box x e.2 (separation o e.1) r hx he
  have hx' := Planned.PrimaryIntegral295.Racks.within he.le hx
  have hz : (wrap n x+o,e.2) = e := by simp [x]
  have hh (z : Cover) (hz : z ∈ box r) (p : PlaqAxes) :
      G.chord (faceValue (expandAt o U) (z,p)) ≤ t := by
    rw [expanded o U z p]
    exact h (wrap n z+o,p) (cell o r hz p)
  have ha := Planned.PrimaryIntegral295.Racks.axle k r t ht (expandAt o U) hh (x,e.2) hx' hv
  calc
    _ = G.chord (Lattice.gauge (traveller (allAxes k) (expandAt o U) 0) (expandAt o U) (x,e.2)) := by
      have h := congrArg G.chord (pull k o U r hn x e.2 hx' hv)
      exact (congrArg (fun a => G.chord (Lattice.gauge (frame k o U) U a)) hz.symm).trans h
    _ ≤ _ := ha.trans_eq (by ring)

/-- A deterministic finite sum of actual plaquette chords bounds every link moment. -/
theorem powers (k : Lattice.Order) (o : Site n) (U : Config G n) (r q : ℕ) (hn : 2*r < n.val)
    (e : Edge (Site n)) (he : separation o e.1 < r) :
    G.chord (Lattice.gauge (frame k o U) U e)^q ≤
      (4*(r:ℝ)*Fintype.card PlaqAxes)^q * ∑ z ∈ cells o r, G.chord (faceValue U z)^q := by
  obtain ⟨z,hz,hm⟩ := Finset.exists_max_image (cells o r) (fun p => G.chord (faceValue U p)) (nonempty o r)
  have h := pow_le_pow_left₀ (G.chord_nonneg _) (bound k o U r hn e he (G.chord_nonneg _) hm) q
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun p _ => pow_nonneg (G.chord_nonneg (faceValue U p)) q) hz) (by positivity))

def indicator (z : Face (Per n)) (t : ℝ) (U : Config G n) : ℝ :=
  (trigger z t).indicator (fun _ => (1:ℝ)) U

theorem measured (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (k : Lattice.Order) (o : Site n)
    (r q : ℕ) (hn : 2*r < n.val) (e : Edge (Site n)) (he : separation o e.1 < r)
    {t δ : ℝ} (ht : 0 ≤ t) (hd : ∀ z ∈ cells o r, μ.real (trigger z t) ≤ δ) :
    (∫ U, G.chord (Lattice.gauge (frame k o U) U e)^q ∂μ) ≤
      (4*(r:ℝ)*Fintype.card PlaqAxes*t)^q + 2^q*((cells o r).card*δ) := by
  let I (U : Config G n) : ℝ := ∑ z ∈ cells o r, indicator z t U
  let C := (4*(r:ℝ)*Fintype.card PlaqAxes*t)^q
  have hi (z : Face (Per n)) : Integrable (indicator z t (G:=G)) μ := (integrable_const 1).indicator (fire_meas _ _)
  have hp (z : Face (Per n)) (U : Config G n) : 0 ≤ indicator z t U := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI : Integrable I μ := integrable_finsetSum _ fun z _ => hi z
  have hsum : (∫ U,I U ∂μ) ≤ (cells o r).card*δ := by
    dsimp only [I]
    rw [integral_finsetSum _ (fun z _ => hi z)]
    calc
      _ ≤ ∑ _z ∈ cells o r, δ := by
        apply Finset.sum_le_sum
        intro z hz
        change (∫ U,(trigger z t).indicator (fun _ : Config G n => (1:ℝ)) U ∂μ) ≤ δ
        rw [integral_indicator (fire_meas _ _),setIntegral_const,smul_eq_mul,mul_one]
        exact hd z hz
      _ = _ := by simp
  have hdom (U : Config G n) : G.chord (Lattice.gauge (frame k o U) U e)^q ≤ C + 2^q*I U := by
    by_cases good : ∀ z ∈ cells o r, G.chord (faceValue U z) ≤ t
    · exact (pow_le_pow_left₀ (G.chord_nonneg _) (bound k o U r hn e he ht good) q).trans
        (le_add_of_nonneg_right (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hp z U)))
    push Not at good
    obtain ⟨z,hz,hz'⟩ := good
    have hzI : indicator z t U = 1 := Set.indicator_of_mem (s:=trigger z t) hz' _
    have hone : 1 ≤ I U := hzI ▸ Finset.single_le_sum (fun p _ => hp p U) hz
    exact (pow_le_pow_left₀ (G.chord_nonneg _) (G.chord_le_two _) q).trans
      ((le_mul_of_one_le_right (by positivity) hone).trans (le_add_of_nonneg_left (by dsimp [C];positivity)))
  calc
    _ ≤ ∫ U,C+2^q*I U ∂μ := integral_mono_of_nonneg (ae_of_all _ fun U => pow_nonneg (G.chord_nonneg _) _)
      ((integrable_const C).add (hI.const_mul _)) (ae_of_all _ hdom)
    _ = C+2^q*(∫ U,I U ∂μ) := by rw [integral_add (integrable_const _) (hI.const_mul _),integral_const,probReal_univ,one_smul,integral_const_mul]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hsum (by positivity)) _

/-- One cofinal threshold precedes every period, cutoff, gauge order, center, and allowed window. -/
theorem original {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m ≤ N → ∀ p, ∀ (k : Lattice.Order) (o : Site (H.S.side m p)) (r q : ℕ),
    2*r < (H.S.side m p).val → ∀ e : Edge (Site (H.S.side m p)), separation o e.1 < r →
    (∫ U, G.chord (Lattice.gauge (frame k o U) U e)^q ∂scene H N p m) ≤
      (4*(r:ℝ)*Fintype.card PlaqAxes*cool H.levels m)^q + 2^q*((cells o r).card*vanishP H.levels m) := by
  filter_upwards [rare P hG Y] with m hm N hN p k o r q hsize e he
  letI : IsProbabilityMeasure (scene H N p m) := probability (H:=H) (p:=p) Y hN
  have ht : 0 ≤ cool H.levels m := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by dsimp only [sigmaU]; positivity)
  exact measured _ k o r q hsize e he ht fun z _ => hm N hN p z

end YM.Integration.WilsonAxialWindow
end
