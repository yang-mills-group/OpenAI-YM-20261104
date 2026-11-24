import YM.WilsonMS.Calibration.Barter
/-!
# Preamble book is equivariant and linear within each h,r

With strict rank grading before transformation. Keep address-zero throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open Function Filter Set MeasureTheory
open MS Plane Koszul Landau Lattice Cylinder Native Native.Chart Lab Orient Native.Paint Book Convolve
  Program Bare
open MS.Cylinder.Taylor
open Tone Color Native.Draft Wilsonian High Knobs Trading HBeam
open XSpace Maxwell Source Menus Webs
open Complex (I)
open scoped Classical Topology ContDiff Interval
variable {G : Gauge} {d r h : ℕ} {H : Source.Hol G} (A : Survey G H d)
section stencil

lemma read_rotate (U : Wilson.CoverConfig G) (s : Signed) (p : Labels.Pol G) :
    reader A p (Lattice.pull s 0 U) = reader A (Labels.rotated s.ortho p) U := by
  unfold reader
  rw [A.reading_signed]
  simp only [Labels.rotated, Labels.eval_changed]
  rw [snap_expand]

lemma turn_name (s : Signed) (p : Labels.Pol G) :
    pose s (Webs.symbol A p) = Webs.symbol A (Labels.rotated s.ortho p) := by
  apply (enterEq ..).mp <| Eventually.of_forall ?_
  intro j
  let P := p
  let u := Labels.rotated s.ortho p
  let F (z : Site j → G.Color) := z
  let v := ORead A j p ∘ nation
  have he : (ORead A j u) ∘ nation = v ∘ affine s := by
    funext i
    simp only [Function.comp_apply, v, ORead, Orient.at_nation, expandAt_pull, Lattice.affine,
      Signed.act_zero, add_zero]
    exact (read_rotate A _ _ _).symm
  simp only [Webs.symbol, map_add, map_smul]
  congr 1
  · rw [paymentR A j]
    change (shown j (pose s (printR A p))).val = _
    rw [travel_t,
      show shown j (printR A p) = region.symm (reads (Complex.re ∘ v)) from
        Subtype.ext (paymentR A j p),
      pose_rule s (f := Complex.re ∘ v) (inkVia A p)]
    rw [Function.comp_assoc (g := ORead A j u), he]
    rfl
  congr 1
  rw [paymentI A j]
  change (shown j (pose s (printI A p))).val = _
  have hV : germ (Complex.im ∘ v) := by
    unfold v
    rw [wrapped]
    let Q := Sew.pull (G := G) (Sew.thread (wrap j) (site A))
    exact
      ContDiffAt.comp (f := ⇑Q) 0 (g := fun x => (reader A p (packetU A x)).im)
        (by
          rw [map_zero]
          exact calm_I A p)
        Q.contDiff.contDiffAt
  rw [travel_t,
    show shown j (printI A p) = region.symm (reads (Complex.im ∘ v)) from
      Subtype.ext (paymentI A j p),
    pose_rule s hV]
  rw [Function.comp_assoc (g := ORead A j u), he]
  rfl

lemma stencil_money (t : ℝ) (p : Labels.Pol G) : Webs.symbol A (t • p) = t • Webs.symbol A p := by
  let g (x : Labels.Pol G) i := reader A x (packetU A i)
  have hv : g (t • p) = t • g p :=
    funext fun i => map_smul ((Labels.read _).toLinearMap.restrictScalars ℝ) t p
  unfold Webs.symbol printR printI
  rw [smul_add, smul_comm t]
  congr 1
  · unfold Sew.art
    rw [show (fun x => (reader A (t • p) (packetU A x)).re) = t • (Complex.re ∘ g p) from
        funext
          (fun x => (congr_arg Complex.re (congr_fun hv x)).trans (map_smul Complex.reCLM t (g p x))),
      ink_smul (e := priv) (f := Complex.re ∘ g p) (calm_R A p), map_smul, map_smul]
    rfl
  congr 1
  unfold Sew.art
  rw [show (fun x => (reader A (t • p) (packetU A x)).im) = t • (Complex.im ∘ g p) from
      funext
        (fun x => (congr_arg Complex.im (congr_fun hv x)).trans (map_smul Complex.imCLM t (g p x))),
    ink_smul (e := priv) (f := Complex.im ∘ g p) (calm_I A p), map_smul, map_smul]
  rfl

def stroke : Labels.Pol G →ₗ[ℝ] Dot G Cover
    where
  toFun := Webs.symbol A
  map_add' := sum_part A
  map_smul' := stencil_money A
end stencil
local notation "B" => Ensure.deck G
variable (W : XSpace.Initialize G) (p : Team)

private def atPart (A : Survey G H d) (i j : ℕ) : Labels.Label G d →ₗ[ℂ] Labels.Label G d :=
  (Labels.gradePart (i, j)).comp (A.insertW (-1) - LinearMap.id)

private def lens (n : ℕ) : Dot G Cover →ₗ[ℂ] T (Dot G Cover) :=
  LinearMap.pi fun i : ℕ => model ((i : ℤ) + n)

def levelGrade (d r : ℕ) : Labels.Label G d →ₗ[ℝ] T (Dot G Cover) :=
  let A := W.surveys d
  let v := stroke A ∘ₗ ((Labels.localFields G d).subtype.restrictScalars ℝ)
  ((lens r).restrictScalars ℝ) ∘ₗ v +
    ∑ i : Fin (d + 1) × Fin r,
      (lens i.2.val).restrictScalars ℝ ∘ₗ v ∘ₗ (atPart A i.1 i.2).restrictScalars ℝ

lemma listed (b : Glyph B d) : levelGrade W b.size b.grade (data0 b) = vertices W b := by
  unfold vertices levelGrade
  rw [LinearMap.add_apply, LinearMap.sum_apply (M := Labels.Label G b.size) (σ₁₂ := RingHom.id ℝ)]
  rfl

lemma level_turn (s : Signed) (v : Labels.Label G d) (r : ℕ) :
    promote (pose s) (levelGrade W d r v) = levelGrade W d r (Labels.tensor s.ortho v) := by
  unfold levelGrade
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  let A := W.surveys d
  have hp (n : ℕ) (v : Labels.Label G d) :
    promote (pose s) (lens n (G := G) (Webs.symbol A v.val)) =
      lens n (Webs.symbol A (Labels.tensor s.ortho v).val) :=
    funext fun i => Eq.trans (poseModel _ s (Webs.symbol A v.val)) (congr_arg _ (turn_name A s v.val))
  refine congr_arg₂ _ (hp _ v) (Finset.sum_congr rfl (fun i _ => ?_))
  let P := atPart (W.surveys d) i.1 i.2
  suffices ht : Labels.tensor s.ortho (P v) = P (Labels.tensor s.ortho v) from
    by
    change promote (pose s) (lens _ (Webs.symbol A (P v).val)) = lens _ (Webs.symbol _ _)
    rw [hp _ (P v), ht]
    rfl
  unfold P atPart
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Labels.gradePart_turn]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, map_sub, ← Survey.wick_signed]

def veil (d r : ℕ) (x : ℝ) : Labels.Label G d →ₗ[ℝ] T (Dot G Cover) :=
  ((wobble G p x).restrictScalars ℝ) ∘ₗ levelGrade W d r

lemma tab (x : ℝ) (u : Glyph B d) : veil W p u.size u.grade x (data0 u) = preambleW W p u x := by
  change wobble _ _ _ _ = _
  rw [listed]
  rfl

lemma veil_turn (s : Signed) (u : Labels.Label G d) (r : ℕ) (x : ℝ) (n : ℕ) :
    pose s (veil W p d r x u n) = veil W p d r x (Labels.tensor s.ortho u) n := by
  change pose s (wobble _ _ _ _ n) = _
  rw [pose_wobble, level_turn]
  rfl
end YM.WilsonMS.BMenu
