import YM.Integration.WilsonGraphSingletonNearRounded

/-! The actual one-near, one-far continuum row for either ordering of the original
    grades. Both lifted fields are read through the same appointed frame and the
    original separated positions. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Function Filter Finset Set Real PowerSeries Growth Continuation Window
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (N g hg) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)
private abbrev grade (h : ℕ) := fun _ : Fin 1 => h

theorem bothPhysical {n m c : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : ∀ i, d i ≤ c) (he : ∀ j, e j ≤ c) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : ℝ) (phase : Viewers (V.{u} g hg periods strict).pupil.last)
      (o : E4) (x : YM.Points n) (y : YM.Points m), placement s (x,y) ∈ YM.conf (n+m) →
      ∀ (u : Inputs g.core d) (v : Inputs g.core e),
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        d e (r,s) (phase,o) x y u v =
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        (fun _ : Fin n => c) (fun _ : Fin m => c) (r,s) (phase,o) x y
        (installedInputs hd u) (installedInputs he v) := by
  let P := V.{u} g hg periods strict
  let U := P.pupil.last
  let J := H.{u} g hg periods strict
  filter_upwards [eventually_all.mpr (fun i => ElectedMeasurement.included P (N g hg) (Q.{u} g hg) (hd i)),
    eventually_all.mpr (fun j => ElectedMeasurement.included P (N g hg) (Q.{u} g hg) (he j)),
    self_mem_nhdsWithin] with r left right positive
  intro s phase o x y safe u v
  let w : Window := (r,s)
  have along : Physical.Round.along w x y = placement s (x,y) := by
    change forest x (w.Stretch • y) = forest x (squeeze (-w.sep) y)
    rw [Physical.Round.wide_here w y]
  have sep : w.len • Physical.Round.along w x y ∈ YM.conf (n+m) := by
    rw [along]
    exact (smul_right_injective E4 (show 0 < r from positive).ne').comp safe
  have original := Physical.Round.named_cap U J sep (phase,o) u v hd he
    (fun i => left i (u i)) (fun j => right j (v j))
  have common := Physical.Round.record U J (phase,o) w x y (installedInputs hd u)
    (installedInputs he v) sep
  exact original.trans common.symm

theorem bothFormal {n m c : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : ∀ i, d i ≤ c) (he : ∀ j, e j ≤ c) (s : ℝ)
    (x : YM.Points n) (u : Inputs g.core d) (y : YM.Points m) (v : Inputs g.core e)
    (safe : placement s (x,y) ∈ YM.conf (n+m)) :
    Continuation.row (N g hg) x u y v s =
      Continuation.row (N g hg) (d := fun _ : Fin n => c) (e := fun _ : Fin m => c)
        x (installedInputs hd u) y (installedInputs he v) s := by
  ext j
  rw [Continuation.coeff_row (Q.{0} g hg).matching x u y v s hd he safe j,
      Continuation.coeff_row (Q.{0} g hg).matching x (d := fun _ : Fin n => c)
        (installedInputs hd u) y (e := fun _ : Fin m => c) (installedInputs he v) s
        (fun _ => le_rfl) (fun _ => le_rfl) safe j]
  rfl

/-- On the original grades, including when the near input has higher grade than its peer. -/
theorem everyGrade (d : Fin 1 → ℕ) (h p : ℕ) (K S : Set (YM.Points 1))
    (near : IsCompact K) (far : IsCompact S) (outside : S ⊆ O.Enh.Outside 1)
    {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    RoundedAt (N g hg) (Physical.Y0 (V.{u} g hg periods strict).pupil.last
      (H.{u} g hg periods strict) d (grade h)) (upper g.core C B) K S
      (heat.{u} g hg periods strict) p := by
  let c := max (d 0) h
  have hd (i : Fin 1) : d i ≤ c := by
    obtain rfl : i=0 := Subsingleton.elim _ _
    exact le_max_left _ _
  have he (j : Fin 1) : grade h j ≤ c := le_max_right _ _
  intro L R
  obtain ⟨L',left⟩ := Physical.Round.hosts (G := g.core) d L hd
  obtain ⟨R',right⟩ := Physical.Round.hosts (G := g.core) (grade h) R he
  obtain ⟨D,hD,a,prices⟩ := roundedAt.{u} g hg periods strict (grade c) c p
    (fun _ => le_rfl) K S near far outside hC hB L' R'
  obtain ⟨T,_,permitted,geometry⟩ := compactExterior near far outside (upper g.core C B)
  have lifts := (windows_short (upper g.core C B)).eventually
    (bothPhysical.{u} g hg periods strict hd he)
  refine ⟨D,hD,a,?_⟩
  filter_upwards [prices,geometry,lifts] with w paid stays raiseAt
  intro i x hx y hy u hu v hv
  have ok : placement w.2 ((0 : YM.Points 1), exterior w.2 x y) ∈ YM.conf 2 :=
    O.Enh.lives (-w.2) (permitted (stays x hx y hy))
  have safe := stageSeparated w.2 x y ok
  have observed : Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
      d (grade h) w i x y u v =
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        (grade c) (grade c) w i x y (installedInputs hd u) (installedInputs he v) :=
    raiseAt w.2 i.1 i.2 x y safe u v
  have coefficients : Continuation.row (N g hg) x u y v (Window.sep w) =
      Continuation.row (N g hg) (d := grade c) (e := grade c) x (installedInputs hd u)
        y (installedInputs he v) (Window.sep w) := bothFormal g hg hd he w.2 x u y v safe
  rw [observed,coefficients]
  exact paid i x hx y hy (installedInputs hd u) (left u hu) (installedInputs he v) (right v hv)

end YM.FVA2.GradedFar.AppointedOneNear
end

