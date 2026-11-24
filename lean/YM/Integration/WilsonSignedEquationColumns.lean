import YM.Integration.WilsonSignedReportPrice
import YM.Integration.WilsonOffsetEquationLaw
import YM.UVExtension.Fallow.Fife

/-! Price the actual difference of whole original insertions.  The stamp is
held fixed before the period, the label, and the finite motion coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSignedEquationColumns
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract Next.Foundations MergeProof PhysicalNext.Repeat.Legato Cells
open Extra.Histories Extra.Multi Motion Push.RelayDifference
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}
local notation "F" => C.labels.level d
local notation "T" => C.localSection d
local notation "ρ" => Motion.Tally (C.labels.level d)
variable (V : SectionData (C.labels.level d))

def piece (N p : ℕ) (U : (F).Index → C.label d) (i : ρ) :=
    initial T C.path N p (Motion.patch F i.1 (U i.2)) 0 -
      initial V C.path N p (Motion.patch F i.1 (Size.axis F i.2)) 0

attribute [local irreducible] Motion.repaint in
private theorem decorated (F₀ : Labels.Frame G d) (v : F₀.Index → F₀.Coeff) (z : F₀.Coeff) :
    decor F₀ v z = repaint F₀ v z := by
  unfold decor
  rfl

theorem expand (N p : ℕ) (P : C.label d ≃ₗ[ℂ] C.label d)
    (U : (F).Index → C.label d) (stamped : ∀ z, P z = decor F U z) (x : C.label d) :
    initial T C.path N p (P x) 0 - initial V C.path N p x 0 =
      ∑ i : ρ, chips F x i • piece V N p U i := by
  let f := IsLinearMap.mk' _ (notationL C.path d F V N p 0)
  let g := IsLinearMap.mk' _ (notationL C.path d F T N p 0)
  change g (P x)-f x=∑ i:ρ, chips F x i • (g (Motion.patch F i.1 (U i.2))-f (Motion.patch F i.1 (Size.axis F i.2)))
  simp_rw [smul_sub,Finset.sum_sub_distrib,←map_smul,←map_sum]
  rw [stamped x,decorated F U x]
  change _=g (repaint F U x)-f (repaint F (Size.axis F) x)
  rw [show repaint F (Size.axis F) x=x from repaint_same F LinearMap.id (fun _ _=>rfl) _]

theorem turn (H : C.Makes) (valid : V.Sound C.params) (N p : ℕ)
    (U : (F).Index → C.label d) (i : ρ) :
    WilsonSignedReportPrice.column V N p U i.2 i.1 = -piece V N p U i := by
  unfold WilsonSignedReportPrice.column piece
  rw [neg_sub,show dance i.1 (initial V C.path N p (Size.axis F i.2) 0 -
      initial T C.path N p (U i.2) 0) =
      dance i.1 (initial V C.path N p (Size.axis F i.2) 0) -
        dance i.1 (initial T C.path N p (U i.2) 0) from
    funext fun A => by unfold dance scalar; split <;> simp]
  rw [signed_intro C V valid,signed_intro C T (H.sections d)]

theorem inside {N p : ℕ} (valid : V.Sound C.params) (o : Site (C.side N p))
    (z : C.label d) :
    Interior (V.footprint o) (initial V C.path N p z o) := by
  unfold initial
  apply Interior.scale
  let a:=(F).scaled (C.path.levels.budget N).threshold⁻¹ z
  exact ⟨V.placed_invariant valid o _,(V.continuous_places a _).measurable,V.placed_local o _,
    (V.continuous_places a _).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

private theorem diff {n : Side} {K : Set (Site n)} {A B : Config G n → ℂ}
    (a : Interior K A) (b : Interior K B) : Interior K (A-B) := by
  change Interior K (fun x => A x - B x)
  simpa only [sub_eq_add_neg,neg_one_mul] using a.plus (b.scale (-1:ℂ))

theorem charged {P : ℕ → ℕ → (C.label d ≃ₗ[ℂ] C.label d)}
    {U : ℕ → ℕ → (C.labels.level d).Index → C.label d} {E : ℕ → ℝ} (H : C.Makes) (valid : V.Sound C.params)
    (h : Hearth V (Bandage.fly C.path.levels) E P U) :
    ∀ᶠ N in atTop, ∀ p k m, C.ref d ≤ k → k < N →
    Stock.Tabs.opens C.path.levels 1 m k → ∀ hm : m ≤ N,
    (↑(V.footprint (0 : Site (C.side N p))) : Set _) ⊆ (center C.S p hm 0).chamber 0 →
    (↑((T).footprint (0 : Site (C.side N p))) : Set _) ⊆ (center C.S p hm 0).chamber 0 →
    ∀ x : C.label d, (center C.S p hm 0).rootTest (C.beta N p)
        (initial T C.path N p (P N p x) 0 - initial V C.path N p x 0) ≤
      (orbitCost F * (F).coeffSize x) *
        (WilsonSignedReportPrice.conversion C d m k * WilsonCutoffDiscrepancyPrice.room C E k) := by
  filter_upwards [h.stamped,WilsonSignedReportPrice.receipt h] with N ns paid
  intro p k m hk hn op hm fV fT x
  let t:=center C.S p hm 0
  let B:= WilsonSignedReportPrice.conversion C d m k * WilsonCutoffDiscrepancyPrice.room C E k
  let A (i : ρ) := piece V N p (U N p) i
  have fit (i : ρ) : Interior (t.chamber 0) (A i) := by
    have ht := (inside T (H.sections d) 0 (Motion.patch F i.1 (U N p i.2))).enlarges fT
    have hv := (inside V valid 0 (Motion.patch F i.1 (Size.axis F i.2))).enlarges fV
    exact diff ht hv
  have bound (i : ρ) : t.rootTest (C.beta N p) (A i) ≤ B := by
    have h' := paid p k m hk hn op i.2 i.1 hm
    rw [turn V H valid N p (U N p) i] at h'
    exact (unitsC _ t (A i) (C.beta N p)).le.trans h'
  have hE := FullVolume.borrowed (W:=E) (h.coined Extraction.Order.full)
  have hroom := (WilsonCutoffDiscrepancyPrice.heard C E hE k).1
  have hB : 0 ≤ B := mul_nonneg (WilsonSignedReportPrice.conversion_pos C d m k).le
    (zero_le_one.trans hroom)
  rw [expand V N p (P N p) (U N p) (ns p).1 x]
  apply (rooted t (C.beta N p) (seamless H N p) Finset.univ A (chips F x) (fun i _ => fit i)).2.trans
  apply (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (bound i) (norm_nonneg _)).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (chipcost F x) hB

end YM.Integration.WilsonSignedEquationColumns
