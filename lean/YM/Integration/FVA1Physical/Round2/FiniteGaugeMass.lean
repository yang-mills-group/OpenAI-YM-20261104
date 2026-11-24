import YM.RG.Bounded
import YM.Gauge.Size

/-! A chart predicate testing finitely many bonds has a volume-independent
Haar mass whenever one gauge enters with a chord margin. The same cylinder
works for the entire set of marked bonds, including disconnected ones. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Set MeasureTheory Finset Lattice RG YM.Wilson
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def ends (B : Finset (Edge (Site n))) : Finset (Site n) :=
  B.image Prod.fst ∪ B.image (fun e => e.1 + step e.2)

theorem ends_card (B : Finset (Edge (Site n))) : (ends B).card ≤ 2*B.card := by
  calc
    _ ≤ (B.image Prod.fst).card+(B.image (fun e => e.1+step e.2)).card := card_union_le ..
    _ ≤ B.card+B.card := Nat.add_le_add card_image_le card_image_le
    _ = _ := (two_mul _).symm

def edgeWindow (B : Finset (Edge (Site n))) (R : ℝ) : Set (Config G n) :=
  {W | ∀ e∈B, G.chord (W e) < R}

theorem edgeWindow_open (B : Finset (Edge (Site n))) (R : ℝ) : IsOpen (edgeWindow (G:=G) B R) := by
  rw [show edgeWindow (G:=G) B R = ⋂ e ∈ B, {W : Config G n | G.chord (W e) < R} by
    ext W;simp [edgeWindow]]
  exact isOpen_biInter_finset fun e _ => isOpen_lt (G.continuous_chord.comp (continuous_apply e)) continuous_const

private theorem cylinder {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (a : ι → G.El) (r : ℝ) :
    (Measure.pi (fun _ : ι => G.probHaar)).real {z | ∀ i∈S, G.chord (z i*(a i)⁻¹) ≤ r}
    = (G.probHaar.real (G.shell r))^S.card := by
  let T := fun i : ι => (fun b : G.El => b*(a i)⁻¹) ⁻¹' G.shell r
  have measure (i : ι) : G.probHaar.real (T i) = G.probHaar.real (G.shell r) :=
    congrArg ENNReal.toReal ((measurePreserving_mul_right G.probHaar (a i)⁻¹).measure_preimage
      (G.shell_meas r).nullMeasurableSet)
  have sets : {z : ι → G.El | ∀ i∈S, G.chord (z i*(a i)⁻¹) ≤ r}
      = Set.univ.pi (fun i : ι => if i∈S then T i else Set.univ) := by
    ext z
    simp only [Set.mem_univ_pi,Set.mem_setOf_eq]
    constructor
    · intro h i;by_cases hi:i∈S
      · simpa only [if_pos hi] using (show z i ∈ T i from h i hi)
      · simp [hi]
    · intro h i hi
      exact (show z i ∈ T i by simpa only [if_pos hi] using h i)
  rw [sets,Measure.real,Measure.pi_pi,ENNReal.toReal_prod]
  have cost i : (G.probHaar (if i ∈ S then T i else Set.univ)).toReal =
      if i∈S then G.probHaar.real (G.shell r) else 1 := by
    by_cases hi : i∈S
    · simp only [if_pos hi];exact measure i
    · simp [hi]
  simp_rw [cost]
  rw [←Finset.prod_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const]

theorem finite_gauge_mass (B : Finset (Edge (Site n))) (W : Config G n) (a : Site n → G.El)
    {r R : ℝ} (pos : 0 < r) (small : r ≤ 1)
    (margin : ∀ e∈B, G.chord (gauge a W e)+2*r < R) :
    (r/4)^(Module.finrank ℝ G.Mat * (2*B.card)) ≤
      (Measure.pi (fun _ : Site n => G.probHaar)).real {z | gauge z W ∈ edgeWindow B R} := by
  let S := ends B
  let μ := Measure.pi (fun _ : Site n => G.probHaar)
  let T : Set (Site n → G.El) := {z | ∀ i∈S, G.chord (z i*(a i)⁻¹) ≤ r}
  have sub : T ⊆ {z | gauge z W ∈ edgeWindow B R} := by
    intro z h e he
    let t := fun i => z i*(a i)⁻¹
    have hl := h e.1 (mem_union_left _ (mem_image_of_mem Prod.fst he))
    have hr := h (e.1+step e.2) (mem_union_right _ (mem_image_of_mem (fun i => i.1+step i.2) he))
    have id : gauge z W e = t e.1*(gauge a W e)*(t (e.1+step e.2))⁻¹ := by
      unfold Lattice.gauge t;group
    rw [id]
    calc
      _ ≤ G.chord (t e.1) + G.chord (gauge a W e) + G.chord ((t (e.1+step e.2))⁻¹) :=
        (G.chord_triangle (t e.1*(gauge a W e)) ((t (e.1+step e.2))⁻¹)).trans
          (add_le_add (G.chord_triangle (t e.1) (gauge a W e)) le_rfl)
      _ ≤ r + G.chord (gauge a W e) + r := by rw [G.chord_inv];exact add_le_add (add_le_add hl le_rfl) hr
      _ < R := by linarith only [margin e he]
  have base : (r/4)^(Module.finrank ℝ G.Mat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [small])
  calc
    _ = ((r/4)^(Module.finrank ℝ G.Mat))^(2*B.card) := pow_mul ..
    _ ≤ ((r/4)^(Module.finrank ℝ G.Mat))^S.card :=
      pow_le_pow_of_le_one (by positivity) base (ends_card _)
    _ ≤ (G.probHaar.real (G.shell r))^S.card := pow_le_pow_left₀ (by positivity) (G.shell_ge r pos small) _
    _ = μ.real T := (cylinder S a r).symm
    _ ≤ _ := measureReal_mono sub

end YM.Integration.FVA1Physical.Round2.Curvature
