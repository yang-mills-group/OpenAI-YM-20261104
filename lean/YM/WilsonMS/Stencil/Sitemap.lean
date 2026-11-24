import YM.WilsonMS.Stencil.DualGrade
/-!
# Emit actual stencil symbols in the MS basis

No minimal-rank truncation of the stencil. All Taylor terms, at the local
anchors. Momentum scaling property deferred while installing the individual insertion tags
from a single set of physical insertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Webs
open Function Filter Finset Set MeasureTheory XSpace
open Lattice RG Maxwell Source Labels Maxwell.Free Wilson
open MS MS.Local MS.Local.Physical MS.Plane MS.Koszul MS.Theater MS.Tone
open MS.Menus MS.Land MS.Local.BV MS.Cylinder MS.Book MS.Native MS.Puff.Actors MS.Landau.Detect
open MS.Native.Sew MS.Native.Studio MS.Native.Wilsonian MS.Native.Chart MS.Native.Draft
  MS.Cylinder.Lab MS.Cylinder.Taylor
open Submodule
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {H : Source.Hol G} {p q : Labels.Pol G} {d l r : ℕ} (A : Survey G H d) {n : Side}

def reader (p : Labels.Pol G) (U : Wilson.CoverConfig G) : ℂ :=
  Labels.read (Drops.expand d (A.reading U)) p

def sites : Finset Cover :=
  univ.biUnion fun j => (A.looks j).stencil

lemma location (p : Labels.Pol G) : LocalOn (A |> sites) (reader A p) := by
  intro U V he
  unfold reader Survey.reading
  apply congr_arg (fun v => Labels.read (Drops.expand _ (A.recover v)) p)
  funext i
  apply Slot.covered _
  intro x hx hv
  exact
    he _ (Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ i, hx⟩)
      (Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ i, hv⟩)

lemma color_inv (hp : p ∈ Labels.invariantSpace G) : Lattice.GaugeInvariant (reader A p) := by
  intro t U
  unfold reader
  rw [A.reading_gauge]
  refine Eq.trans (congr_arg (fun x => Labels.read x p) ?_) (hp _ (t 0))
  funext i
  by_cases he : i < d - 1 <;> simp [Drops.expand, Labels.colored, Drops.Cast, he]

lemma continuous_reader (p : Labels.Pol G) : Continuous (reader A p) :=
  Continuous.comp (f := A.reading) (g := fun x => Labels.read (Drops.expand d x) p)
    (Work.G05.snap_read_smooth d p ω |>.continuous)
    (A.recover_smooth.continuous.comp (continuous_pi fun i => Slot.cont (A.looks i)))

abbrev Wire :=
  ↥(sites A) × Axis

def site (v : Wire A) : Edge Cover :=
  (v.1.val, v.2)

def spread (a : Wire A → G.El) (e : Edge Cover) :=
  if h : e.1 ∈ sites A then a (⟨e.1, h⟩, e.2) else 1

lemma photographed (p : Labels.Pol G) (U : Wilson.CoverConfig G) :
    reader A p U = reader A p (spread A (U ∘ site A)) :=
  location A p U _ fun e h _ => by
    have ht : e.1 ∈ sites A := h
    simp [spread, ht, site]

def packetU (V : Lot G (Wire A)) :=
  spread A (G.lieExp ∘ V)

lemma mat_smooth (e : Edge Cover) : ContDiff ℝ ω (fun V : Lot G (Wire A) => G.mat (packetU A V e)) := by
  unfold packetU spread
  split
  exact G.exp_jet.comp (f := fun (W : Lot G (Wire A)) => W _) (contDiff_apply ..)
  exact contDiff_const

lemma slot_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → CoverConfig G} (he : ∀ e, ContDiff ℝ ω (fun a => G.mat (f a e))) (J : Slot) :
    ContDiff ℝ ω (fun a => J.eval (f a)) := by
  have he' (x : Cover) (p : Walk) : ContDiff ℝ ω (fun a => G.mat (travel (f a) x p)) := by
    induction p generalizing x with
    | nil => exact contDiff_const
    | cons t p ih =>
      simp_rw [travel, G.mat_mul]
      apply ContDiff.mul _ (ih _)
      unfold Step.read
      split
      · simp_rw [G.mat_inv]
        exact ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff).comp (he _)
      exact he _
  unfold Slot.eval
  simp_rw [← G.curvature_conjugate]
  let V := G.projectColor.toContinuousLinearMap
  have L :
    ContDiff ℝ ω
      (fun a =>
        G.mat
          (travel (f a) 0 J.walk * faceValue (f a) (J.offset, J.plaq) *
            (travel (f a) 0 J.walk)⁻¹)) := by
    simp_rw [G.mat_mul, G.mat_inv]
    let hp := he' 0 J.walk
    exact
      (hp.mul (he' J.offset (square J.plaq.val.1 J.plaq.val.2))).mul
        ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp hp)
  unfold Gauge.curvature
  simp_rw [G.mat_inv]
  exact
    V.contDiff.comp (((L.sub ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp L)).const_smul (1 / 2 : ℝ)))

lemma sample_smooth : ContDiff ℝ ω (fun a => A.reading (packetU A a)) := by
  refine
    A.recover_smooth.comp (f := fun p => Bid.mapped A.looks (packetU A p))
      (contDiff_pi.mpr fun i => ?_)
  change ContDiff ℝ ω (fun a => Slot.eval (A.looks i) (packetU A a))
  exact slot_smooth (mat_smooth A) (A.looks i)

lemma packet_smooth (p : Labels.Pol G) : ContDiff ℝ ω (fun a => reader A p (packetU A a)) :=
  ContDiff.comp (g := fun x => Labels.read (Drops.expand _ x) p) (f := fun a =>
    A.reading (packetU A a)) (Work.G05.snap_read_smooth d p ω) (sample_smooth A)

def ORead (n : Side) (p : Labels.Pol G) : Config G n → ℂ := fun U =>
  reader A p (expandAt (0 : Site n) U)

lemma cont_OR (n) (p : Labels.Pol G) : Continuous (ORead A n p) := by
  unfold ORead
  exact (continuous_reader A p).comp (f := expandAt 0) (continuous_pi fun _ => continuous_apply _)

lemma wrapped (n : Side) (p : Labels.Pol G) :
    ORead A n p ∘ nation = reader A p ∘ packetU A ∘ Sew.pull (thread (wrap n) (site A)) := by
  ext1 U
  unfold ORead
  simp_rw [Function.comp_apply]
  rw [photographed A p]
  apply congr_arg (reader A p)
  unfold packetU
  congr 1
  ext1 e
  unfold expandAt
  simp only [Function.comp_apply, add_zero]
  rfl

lemma is_real (hp : Labels.conjPol p = p) (U : CoverConfig G) :
    reader A p U = (((reader A p U).re : ℝ) : ℂ) := by
  let a := reader A p U
  have h : star a = a := (Labels.conj_value _ _).symm.trans (congr_arg _ hp)
  change a = _
  apply Complex.ext
  · rfl
  rw [Complex.ofReal_im]
  have e := congr_arg Complex.im h
  change -a.im = a.im at e
  linarith

def printR (p : Labels.Pol G) : Dot G Cover :=
  art (site A) (fun x => (reader A p (packetU A x)).re)

def printI (p : Labels.Pol G) : Dot G Cover :=
  art (site A) (fun x => (reader A p (packetU A x)).im)

def symbol (p : Labels.Pol G) : Dot G Cover :=
  printR A p + Complex.I • printI A p

lemma sym_real (hp : Labels.conjPol p = p) : symbol A p = printR A p := by
  unfold symbol printI
  rw [show (fun x => (reader A p (packetU A x)).im) = (0 : Lot G (Wire A) → ℝ) from
      (funext fun x => by
        rw [is_real A hp]
        rfl),
    Sew.art, ink_zero, map_zero, map_zero, smul_zero, add_zero]

lemma calm_R (p : Labels.Pol G) : germ (fun x => (reader A p (packetU A x)).re) :=
  (Complex.reCLM.contDiff.comp (packet_smooth A p)).contDiffAt

lemma calm_I (p : Labels.Pol G) : germ (fun x => (reader A p (packetU A x)).im) :=
  (Complex.imCLM.contDiff.comp (packet_smooth A p)).contDiffAt

lemma paymentR (j : Side) (p : Labels.Pol G) :
    enters j (printR A p) = Native.reads ((Complex.re ∘ ORead A j p) ∘ nation) := by
  unfold printR
  rw [enters_gorge (n := j) _ _ (calm_R A p), Function.comp_assoc, wrapped]
  rfl

lemma paymentI (j : Side) (p : Labels.Pol G) :
    enters j (printI A p) = Native.reads ((Complex.im ∘ ORead A j p) ∘ nation) := by
  unfold printI
  rw [enters_gorge (n := j) _ _ (calm_I A p), Function.comp_assoc, wrapped]
  rfl

lemma inkVia (p : Labels.Pol G) {j : Side} : germ ((Complex.re ∘ ORead A j p) ∘ nation) := by
  rw [Function.comp_assoc, wrapped]
  let Q := Sew.pull (G := G) (thread (wrap j) (site A))
  exact
    ContDiffAt.comp (f := ⇑Q) 0 (g := fun x => (reader A p (packetU A x)).re)
      (by
        rw [map_zero]
        exact calm_R A p)
      Q.contDiff.contDiffAt

lemma sum_part (p q : Labels.Pol G) : symbol A (p + q) = symbol A p + symbol A q := by
  let F := fun (p : Labels.Pol G) x => reader A p (packetU A x)
  have he : F (p + q) = F p + F q := funext fun x => map_add ..
  unfold symbol printR printI Sew.art
  rw [show (fun x => (reader A (p + q) (packetU A x)).re) = (Complex.re ∘ F p) + (Complex.re ∘ F q)
      from funext fun x => congr_arg Complex.re (congr_fun he x),
    show (fun x => (reader A (p + q) (packetU A x)).im) = (Complex.im ∘ F p) + (Complex.im ∘ F q) from
      funext fun x => congr_arg Complex.im (congr_fun he x)]
  rw [ink_add _ (f := Complex.re ∘ F p) (f' := Complex.re ∘ F q) (calm_R A p) (calm_R A q),
    ink_add _ (f := Complex.im ∘ F p) (f' := Complex.im ∘ F q) (calm_I A p) (calm_I A q)]
  simp only [map_add, smul_add]
  unfold F
  change (printR A p + printR A q) + (Complex.I • printI A p + Complex.I • printI A q) = _
  change _ = (symbol A p) + (symbol A q)
  simp only [symbol]
  abel

lemma symbol_X (i : Labels.Key G) : symbol A (MvPolynomial.X i) = printR A (MvPolynomial.X i) :=
  sym_real A (by rw [Labels.conjPol, MvPolynomial.map_X])

lemma product_X (i : Labels.Key G) (p : Labels.Pol G) :
    symbol A (MvPolynomial.X i * p) = couple DotFlip (symbol A (MvPolynomial.X i)) (symbol A p) := by
  let j : Labels.Pol G := MvPolynomial.X i
  let X (x : Labels.Pol G) (z) := reader A x (packetU A z)
  let R (x : Labels.Pol G) := Complex.re ∘ X x
  let I (x : Labels.Pol G) := Complex.im ∘ X x
  have hp (z) : X (j * p) z = ((R j z) : ℂ) * X p z := by
    unfold X reader
    rw [_root_.map_mul]
    congr 1
    exact is_real A (p := j) (by simp [j, Labels.conjPol]) _
  have he : R (j * p) = R j * R p :=
    funext fun z => by
      change (X (j * p) z).re = R j z * _
      rw [hp]
      simp [Complex.mul_re]
      left
      rfl
  have hv : I (j * p) = R j * I p :=
    funext fun z => by
      change (X (j * p) z).im = R j z * _
      rw [hp]
      simp [Complex.mul_im]
      left
      rfl
  have hx (f g : Lot G (Wire A) → ℝ) (hF : germ f) (hG : germ g) :
    art (site A) (f * g) = couple DotFlip (art (site A) f) (art (site A) g) := by
    let p : Sector (Wire A × Conn G) := fun _ => false
    unfold Sew.art
    rw [ink_mul _ (p := p) (fun i hx => Bool.noConfusion hx) hF hG]
    exact
      Cylinder.ferry_pair (Sew.knot (site A) (G := G)) (p := p) (q := DotFlip) (fun _ => rfl)
        (region.symm (ink priv f)) (region.symm (ink priv g))
  rw [symbol_X]
  change
    art (site A) (R (j * p)) + Complex.I • art (site A) (I (j * p)) =
      couple DotFlip (art (site A) (R j)) (art (site A) (R p) + Complex.I • art (site A) (I p))
  rw [map_add, map_smul, he, hv, hx (R j) (R p) (calm_R A j) (calm_R A p),
    hx (R j) (I p) (calm_R A j) (calm_I A p)]

lemma symbol_C (c : ℂ) : symbol A (MvPolynomial.C c) = Cylinder.piece c := by
  let p : Labels.Pol G := MvPolynomial.C c
  have he : (fun x => reader A p (packetU A x)) = (fun _ => c) := by
    ext1 x
    simp [reader, p, Labels.read]
  have ht (v : ℝ) : art (site A) (G := G) (fun _ => v) = Cylinder.piece (v : ℂ) := by
    unfold Sew.art
    rw [ink_const]
    exact coin_settled ..
  change
    art (site A) (Complex.re ∘ fun x => reader A p (packetU A x)) +
        Complex.I • art (site A) (Complex.im ∘ fun x => reader A p (packetU A x)) =
      Cylinder.piece c
  rw [he]
  change Sew.art (site A) (fun _ => c.re) + Complex.I • Sew.art (site A) (fun _ => c.im) = _
  rw [ht, ht]
  apply Subtype.ext
  funext i
  cases i
  · change _ + Complex.I * (↑c.im : ℂ) = _
    rw [mul_comm]
    exact Complex.re_add_im c
  change (0 : ℂ) + Complex.I * 0 = 0
  ring

lemma starts_X (i : Labels.Key G) : From (symbol A (MvPolynomial.X i)).val 1 := by
  intro l he
  have hh : l = [] := List.length_eq_zero_iff.mp (by omega)
  subst l
  rw [symbol_X, printR, Sew.art]
  change shade _ _ [] = 0
  rw [shade_nil]
  change ↑((reader A (MvPolynomial.X i) (packetU A 0)).re) = (0 : ℂ)
  unfold reader
  rw [show A.reading (packetU A 0) = 0 from ?_, Labels.read, MvPolynomial.aeval_X]
  simp [Labels.coord, Drops.expand]
  · split_ifs with h <;> simp
  unfold Survey.reading
  rw [Function.comp_apply, show Bid.mapped A.looks (packetU A 0) = 0 from ?_, A.recover_zero]
  ext1 i
  have hg : packetU A 0 = 1 := by
    ext1 i
    unfold packetU spread
    split <;> simp
  have hr : ∀ (x : Cover) (p : Walk), travel (1 : Links ℤ G.El) x p = 1 := by
    intro x l
    induction l generalizing x with
    | nil => rfl
    | cons d p ih =>
      rw [travel, ih, mul_one]
      unfold Step.read
      split <;> simp
  rw [hg]
  unfold Bid.mapped RG.Slot.eval faceValue
  rw [hr, hr, Gauge.curvature_unit, map_zero]
  rfl

lemma starts (hp : At p (l, r)) : From (symbol A p).val r := by
  apply axisI (fun u p => From (symbol A p).val ↑u.2) hp
  · rintro b w h
    change (w.length : ℤ) < 0 at h
    omega
  · intro i
    rw [show symbol A 0 = 0 from
        add_left_cancel (b := symbol A 0) (c := 0) (a := symbol A 0)
          (by rw [← sum_part, add_zero, add_zero])]
    exact fun _ _ => rfl
  · intro x i f ht he
    rw [product_X, coupled, Prod.snd_add, Nat.cast_add]
    exact (starts_X A i).pair he
  intro x u v _ _ hu hv
  rw [sum_part]
  exact hu.add hv

lemma esteem (hp : p ∈ Film0 G l r) : Aura (symbol A p) r := by
  obtain ⟨hp, h, hq⟩ := (cinema p).mp hp
  refine ⟨starts A hp, ?_, fun n => ?_⟩
  · rw [sym_real A hq]
    exact Tune_port _ _ (calm_R A p)
  refine ⟨Complex.re ∘ ORead A n p, ?_, inkVia A p, ?_⟩
  swap
  · rw [sym_real A hq]
    exact paymentR ..
  intro a U
  rw [show siteGauge _ a U = Lattice.gauge (a⁻¹) U from ?_]
  unfold ORead
  simp_rw [Function.comp_apply, expandAt_gauge]
  exact congr_arg Complex.re (color_inv A h _ _)
  ext1 i
  simp [siteGauge, Chart.drive, endRail, Lattice.gauge]

end YM.WilsonMS.Webs
