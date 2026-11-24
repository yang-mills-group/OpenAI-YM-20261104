import YM.Integration.WilsonPhysicalMarkedDefectStoredField
import YM.MergeProof.South.Loft
import YM.MergeProof.Glacier

/-! The complete occupied coefficient of the physical marked heat history.
The vacuum is the actual Wilson vacuum at birth.  The grade calibration
is undone only after taking the full occupied coefficient on that history. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.StoredGallery

open Function Finset MeasureTheory Lattice Wilson RG Push Push.GridApprox Marker Cells Source
open Extra.Histories RG16.Literal Trace.Physical.GermGraph MergeProof.Accent StoredField
open scoped Classical BigOperators Topology

variable {G : Gauge} (C : Family G) (N p : ℕ) {I : Type} [Fintype I] [DecidableEq I]
variable {d : I → ℕ}

/-- Each mark is placed at its actual physical site with the prescribed
complex calibration.  The fine Wilson actions multiplying this polynomial
are the actions of the same trajectory that produced the stored record. -/
def mark (o : I → Site (C.side N p)) (a : Choice C d) (cal : I → ℂ) (i : I)
    (U : Config G (C.side N p)) : ℂ :=
  cal i * (C.localSection (a i).1.val).places (Pi.single (a i).2 1) (o i) U

def top (B : Census I) (o : I → Site (C.side N p)) (a : Choice C d) (cal : I → ℂ) :=
  birth B (C.path.rep N p N) (mark C N p o a cal)

theorem birth_mode (law : C.Makes) (B : Census I) (o : I → Site (C.side N p))
    (a : Choice C d) (cal : I → ℂ) (s : B.Mode) (U : Config G (C.side N p)) :
    (top C N p B o a cal U).part s =
      (bare (C.beta N p) U : ℂ) * ((∏ i ∈ s.val, cal i) *
        ∏ i ∈ s.val, (C.localSection (a i).1.val).places (Pi.single (a i).2 1) (o i) U) := by
  simp only [top,birth,Poly.part_smul,Mach,Extra.Trajectories.pass_fire,
    (law.wilson.starts N p).2,mark,Finset.prod_mul_distrib]

theorem live (law : C.Makes) (B : Census I) (o : I → Site (C.side N p))
    (a : Choice C d) (cal : I → ℂ) :
    Integrable (top C N p B o a cal) (prior G _) := by
  have vacuum : Continuous (C.path.rep N p N).eval := by
    rw [(law.wilson.starts N p).2]
    exact bare_cont _
  exact (hatCont C N p _ (fun _ => continuous_const.mul (SectionData.continuous_places ..))
    vacuum B).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def field {b : ℕ} (B : Census I) (o : I → Site (C.side N p)) (a : Choice C d)
    (cal : I → ℂ) (hb : b ≤ N) :=
  gust C.path N p N (top C N p B o a cal) b hb

/-- No independent per-spectator cancellation is used.  This is an exact
equality on every original coarse configuration on the true physical path. -/
theorem occupied (law : C.Makes) {h b : ℕ} (B : Census I) (o : I → Site (C.side N p))
    (a : Choice C d) (cal : I → ℂ) (s : B.Mode) (hs : s.val = univ) (hb : b ≤ N) :
    ∀ U, ((C.S.a b : ℂ)^h) * (field C N p B o a cal hb U).part s =
      (∏ i, cal i) * credit C N p h (basisProduct C N p o a) b hb U := by
  let k := ∏ i, cal i
  let f := basisProduct C N p o a
  have seed : (fun U => (top C N p B o a cal U).part s) =
      fun U => (bare (C.beta N p) U : ℂ) * (k • f) U := by
    funext U
    rw [birth_mode C N p law B o a cal s U,hs]
    rfl
  have pushed := gust_choose C.path N p (k:=b) (j:=N) (top C N p B o a cal)
    (live C N p law B o a cal) hb s
  have linear : credit C N p h (k • f) b hb = k • credit C N p h f b hb := by
    simpa using IntrinsicProductLinearity.credit_sum C N p h b hb (fun _ : Unit => k)
      (fun _ : Unit => f) (fun _ => basis_continuous C N p o a)
  intro U
  calc
    _ = credit C N p h (k • f) b hb U := by
      have point := congrFun (pushed.trans (congrArg (pushTo C.path N p hb) seed)) U
      exact congrArg (((C.S.a b : ℂ)^h) * ·) point
    _ = _ := congrFun linear U

theorem stored {h b J : ℕ} (law : C.Makes) (B : Census I) (s : B.Mode) (hs : s.val = univ)
    (q : Grades C d) (o : I → Site (C.side N p)) (cal : Choice C d → I → ℂ)
    (hne : ∀ a i, cal a i ≠ 0) (hj : J ≤ b) (hb : b ≤ N) (w : Site (C.side J p) → ℝ)
    (Q : store C h p b) {fare : ℝ} (admitted : reads h N p b Q fare)
    (issued : Fleet C N p h b J (product C N p q o) (hj.trans hb) w Q hb) :
    ∀ U, Q.density 0 (C.localSection h) (C.path.rep N p b) U / ((C.path.rep N p b).eval U : ℂ) =
      ∑ a : Choice C d, (weight C N p q a / ∏ i, cal a i) * (C.S.a b : ℂ)^h *
        ((field C N p B o a (cal a) hb U).part s / ((C.path.rep N p b).eval U : ℂ)) := by
  intro U
  rw [bank C N p law q o hj hb w Q admitted issued U]
  apply Finset.sum_congr
  · ext a
    simp only [mem_univ]
  intro a _
  have nz : (∏ i,cal a i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hne a i)
  have exactRow := occupied C N p (h:=h) law B o a (cal a) s hs hb U
  simp only [div_eq_mul_inv]
  calc
    _ = ((weight C N p q a) * (∏ i,cal a i)⁻¹) *
        (((∏ i,cal a i) * credit C N p h (basisProduct C N p o a) b hb U) *
          ((C.path.rep N p b).eval U : ℂ)⁻¹) := by field_simp [nz]
    _ = _ := by rw [← exactRow]; ring

end YM.Integration.WilsonPhysicalMarkedDefect.StoredGallery

