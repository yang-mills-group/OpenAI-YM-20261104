import YangMills.PerturbativeMatching.VolumeLimits
import YangMills.WilsonProof.WilsonBridge
import YM.FullVolume.Profiles

noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching Filter Set MeasureTheory
open scoped Topology Classical ContDiff

variable {g : GaugeGroup} (C : YM.Family g.core) {n : ℕ}

private theorem fullChoose (i : ℕ) : YM.Extraction.Sequence.full.choose i = i := rfl

private theorem pairing (t : SeparatedTest n) (f : Points n → ℂ) :
    YM.Test.applyTo t f = ∫ x : Points n, t x * f x := rfl

private def reach (s : Mesh.Step n) : YM.FullVolume.Reach n :=
  ⟨(s.slot, s.axis), s.back, s.forward, s.nonempty⟩

private theorem differences (h : ℝ) (steps : List (Mesh.Step n)) (f : Grid n → ℂ) :
    Mesh.differences h steps f = YM.FullVolume.squall h (steps.map reach) f := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    funext z
    simp only [Mesh.differences, List.map_cons, YM.FullVolume.squall, YM.FullVolume.Reach.difference, ih]
    simp only [reach, YM.FullVolume.Reach.e, YM.FullVolume.Reach.axis_, YM.FullVolume.drive,
      YM.Lattice.step, Complex.ofReal_mul, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

private theorem derivatives (steps : List (Mesh.Step n)) (f : Points n → ℂ) :
    Mesh.derivatives steps f = YM.FullVolume.derive f ((steps.map reach).map YM.FullVolume.Reach.where_) := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    simp only [Mesh.derivatives, List.map_cons, YM.FullVolume.derive, ih]
    rfl

private theorem gridMoment (N p : ℕ) (v : Fin n → C.book.Token) :
    Mesh.moment (YangMills.wilsonFamily C) N p v = YM.Extraction.lifted C N p v := by
  funext z
  exact YangMills.moment_eq C N p v _

private theorem interp (N : ℕ) (f : Grid n → ℂ) (x : Points n) :
    Mesh.interpolate ((YangMills.wilsonFamily C).mesh N) f x = YM.FullVolume.interpolated C.S N f x := rfl

private theorem testedStencil (p N : ℕ) (t : SeparatedTest n) (F : ℕ → Grid n → ℂ) :
    Mesh.smear (YangMills.wilsonFamily C) N p t (F N) = YM.FullVolume.sumOn F C.S p N t := rfl

/-- Take the smooth row on the original full cutoff sequence. Uniqueness along
the same rounded grid identifies its restriction with the filed period table. -/
theorem smoothOnAppointedRow
    (row : (p n : ℕ) → (Fin n → C.book.Token) → Points n → ℂ)
    (full : YM.FullVolume.PositionsUV C YM.Extraction.Sequence.full)
    (filed : ∀ p n (v : Fin n → C.book.Token), YM.FullVolume.Cluster C .full p n
      (fun N => YM.Extraction.lifted C N p v) (row p n v)) :
    SmoothMeshLimit (YangMills.wilsonFamily C) (fun p {n} v x => row p n v x.val) := by
  intro p n v
  obtain ⟨f, smooth, smears, stencils⟩ := full p n v
  refine ⟨f, smooth, ?_, ?_, ?_⟩
  · intro z
    have safe : z.val ∈ YM.Extraction.NoHit C.S p n :=
      (YM.Extraction.no_wrap_hit C.S (show z.val ∈ YM.Extraction.Inside C.S p n from z.property.2)).2 z.property.1
    let atGrid := fun N => YM.Extraction.address (C.S.a N) z.val
    have near := YM.Extraction.chosen (S := C.S) z.val
    have empty := (stencils []).1.2 z.val safe atGrid id tendsto_id near
    have same := (filed p n v).2 z.val safe atGrid id tendsto_id near
    exact tendsto_nhds_unique empty same
  · intro t ht
    have paid := smears t ht
    simp only [fullChoose, pairing] at paid
    simp_rw [YangMills.smear_eq]
    exact paid
  · intro steps
    let F := fun N => YM.FullVolume.squall (C.S.a N) (steps.map reach) (YM.Extraction.lifted C N p v)
    have native := stencils (steps.map reach)
    have eqF (N : ℕ) : Mesh.differences ((YangMills.wilsonFamily C).mesh N) steps
        (Mesh.moment (YangMills.wilsonFamily C) N p v) = F N := by rw [differences, gridMoment]; rfl
    dsimp only
    rw [derivatives]
    simp_rw [eqF]
    refine ⟨native.1.1, native.1.2, ?_, ?_⟩
    · intro K compact inside ε positive
      simpa only [F, interp, fullChoose] using native.2.1.uniform K inside compact ε positive
    · intro t ht
      have paid := native.2.2 t ht
      simp only [fullChoose, pairing] at paid
      rw [show (fun N => Mesh.smear (YangMills.wilsonFamily C) N p t (F N)) =
            (fun N => YM.FullVolume.sumOn F C.S p N t) from funext fun N => testedStencil C p N t F]
      exact paid

end YangMills.WilsonProof
