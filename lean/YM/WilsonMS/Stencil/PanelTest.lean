import YM.WilsonMS.Stencil.LinkAt
import YM.XSpace.Section
/-!
# Following a field with the actual section cylinders

Keep both gauge change and stencil at arbitrary weights. On each
r-banded tuple of weights combine powers at the end.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Panel
open Function Filter Set MeasureTheory
open Lattice Wilson RG Source Paths Labels RGerm Webs Curves TaylorRules TPath Work XSpace
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {B : Paths.Family G} {A : Axis → E4 → G.Color} {p : Labels.Pol G} {H : Hol G}
  {n l N : ℕ}

def coarse (A : Axis → E4 → G.Color) (t : ℝ) (e : Edge Cover) :=
  G.lieExp (t • A e.2 (travelV e (t, 1 / 2)).2)

def unraised (B : Paths.Family G) (t : ℝ) (e : Edge Cover) :=
  chainU e B t 1

def siteTurn (B : Paths.Family G) (t : ℝ) (x : Cover) :=
  radialG B (t, t • Work.G03.castPos x)

lemma begins (e : Edge Cover) (a : ℝ) : travelV e (a, 0) = (a, a • G03.castPos e.1) := by
  unfold travelV alongFrom Webs.Midpt.station
  simp

lemma finishes (e : Edge Cover) (a : ℝ) :
    travelV e (a, 1) = (a, a • G03.castPos (e.1 + Lattice.step e.2)) := by
  unfold travelV alongFrom Webs.Midpt.station
  simp [G03.castPos_step]

lemma commutes (e : Edge Cover) (a : ℝ) :
    changedU e B a 1 = Lattice.gauge (siteTurn B a) (unraised B a) e := by
  rw [changedU, begins, finishes]
  rfl

variable {U V : ℝ → CoverConfig G}

abbrev synchronized (U V : ℝ → CoverConfig G) (n : ℕ) :=
  ∀ e, Agree n 0 (fun t => G.mat (U t e)) (fun t => G.mat (V t e))

lemma staged (he : synchronized U V n) (p : Walk) (x : Cover) :
    Agree n 0 (fun t => G.mat (travel (U t) x p)) (fun t => G.mat (travel (V t) x p)) := by
  induction p generalizing x with
  | nil => exact Agree.refl contDiffAt_const
  | cons b p ih =>
    simp_rw [travel, G.mat_mul]
    apply Agree.mul _ (ih _)
    unfold Step.read
    split
    · simp_rw [G.mat_inv]
      exact
        (he _).apply_smooth (u := (starL ℝ : G.Mat ≃L[ℝ] G.Mat))
          (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt
    exact he _

lemma measured (he : synchronized U V n) (s : RG.Slot) :
    Agree n 0 (fun t => s.eval (U t)) (fun t => s.eval (V t)) := by
  let W (U : CoverConfig G) :=
    travel U (0 : Cover) s.walk * faceValue U (s.offset, s.plaq) * (travel U (0 : Cover) s.walk)⁻¹
  have h : Agree n 0 (fun t => G.mat (W (U t))) (fun t => G.mat (W (V t))) := by
    unfold W
    simp_rw [G.mat_mul, G.mat_inv]
    exact
      ((staged he ..).mul (staged he ..)).mul
        ((staged he ..).apply_smooth (u := (starL ℝ : G.Mat ≃L[ℝ] G.Mat))
          (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt)
  unfold Slot.eval
  simp_rw [← G.curvature_conjugate, Gauge.curvature, G.mat_inv]
  refine h.apply_smooth (u := fun X => G.projectColor ((1 / 2 : ℝ) • (X - star X))) ?_
  exact
    G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _
      ((contDiffAt_id.sub (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt).const_smul (1 / 2 : ℝ))

lemma sampled (he : synchronized U V n) (K : XSpace.Survey G H N) (p : Pol G) :
    Agree n 0 (fun t => Webs.reader K p (U t)) (fun t => Webs.reader K p (V t)) := by
  let f (t) := Bid.mapped K.looks (U t)
  let g (t) := Bid.mapped K.looks (V t)
  have hp : Agree n 0 f g := Agree.pi_jet fun i => measured he (K.looks i)
  exact
    (hp.apply_smooth (K.recover_smooth.contDiffAt.of_le le_top) (n := n)).apply_smooth
      (Work.G05.snap_read_smooth N p _ |>.contDiffAt)

lemma transformed (h : Flow B) (e : Edge Cover) :
    Agree n 0 (fun t => G.mat (Lattice.gauge (siteTurn B t) (unraised B t) e))
      (fun t : ℝ => G.mat (H.links n (records h t) t e)) := by
  simp_rw [← commutes e]
  exact profileH e h H

lemma columns_lift (h : Flow B) (K : XSpace.Survey G H n) (p : Label G n) :
    Agree n 0 (fun t => reader K p.val (unraised B t))
      (fun t : ℝ => reader K p.val (H.links n (records h t) t)) := by
  have hu :
    (fun t => reader K p.val (unraised B t)) =
      (fun t => reader K p.val (Lattice.gauge (siteTurn B t) (unraised B t))) :=
    funext fun i => Eq.symm (Webs.color_inv K p.property.2 _ _)
  rw [hu]
  exact
    sampled (U := fun t => Lattice.gauge (siteTurn B t) (unraised B t)) (fun e => transformed h e) K _

lemma midpoint_read (K : XSpace.Survey G H n) (p : Pol G) (hf : Flow B) (hp : ∀ i, ContDiff ℝ ∞ (A i))
    (he : Matches A B n) :
    Agree n 0 (fun t => reader K p (coarse A t)) (fun t => reader K p (unraised B t)) := by
  refine sampled (U := coarse A) (V := unraised B) ?_ K p
  intro e
  let f (t : ℝ) := travelV e (t, (1 / 2 : ℝ))
  have hz : f 0 = (0, 0) := by simp [f, travelV]
  have hv :=
    Agree.comp
      (Agree.refl
        (show ContDiffAt ℝ (↑n) f 0 from
          contDiffAt_infty.mp
            (motion_smooth.contDiffAt.comp (f := fun t : ℝ => (t, (1 / 2 : ℝ))) _ (by fun_prop)) n))
      (show
        Agree n (f 0) (fun x => G.mat (G.lieExp (feed (A e.2) x))) (fun x => G.mat (endLink B e.2 x))
        from
        (by
          rw [hz]
          exact realized he hf hp))
  unfold unraised
  simp_rw [from_mid]
  exact hv
section jet
open Source.Drops G05
variable {v : Label G n}

lemma scales_here (hp : v ∈ Grade (N, l)) (J : Jet G) (t : ℝ) :
    read (scaleJet J t) v.val = t ^ N • read J v.val := by
  have he (m : Key G →₀ ℕ) (c : ℂ) :
    read (scaleJet J t) (MvPolynomial.monomial m c) =
      t ^ (height m) • read J (MvPolynomial.monomial m c) := by
    simp only [Labels.read, MvPolynomial.aeval_monomial, Next.Foundations.coord_scales, Finsupp.prod,
      Complex.real_smul, Complex.ofReal_pow, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    unfold height
    rw [Finsupp.weight_apply]
    simp only [Finsupp.sum, smul_eq_mul]
    simp_rw [mul_comm (generation (G := G) _) (m _)]
    ring
  rw [v.val.as_sum, map_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := (pure_grade _ v).mp hp (MvPolynomial.mem_support_iff.mp hi)
  rw [he,
    show height i = N from Eq.trans (congr_arg Prod.fst (weight_slot i)).symm (congr_arg Prod.fst hm)]

lemma book (K : XSpace.Survey G H n) (h : Flow B) (p : Label G n) :
    Agree n 0 (fun t : ℝ => reader K p.val (H.links n (records h t) t))
      (fun t => read (scaleJet (records h t) t) p.val) := by
  letI : CompleteSpace (Snap G n) := FiniteDimensional.complete ℝ _
  let Y (t : ℝ) := trunk n (scaleJet (records h t) t)
  let Q := bring H n K.looks
  let f := K.sees
  let R := fun x : Snap G n => read (expand n x) p.val
  have h0 : Y 0 = 0 := by
    unfold Y trunk scaleJet
    funext i
    simp
  have hf : ContDiffAt ℝ (↑n) f 0 := K.kit.1.contDiffAt.of_le le_top
  have T {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ → F) (k : ℕ)
    (h : ContDiffAt ℝ (↑n) g 0) : ContDiffAt ℝ (↑n) (fun t : ℝ => t ^ k • g t) 0 :=
    (contDiffAt_id.pow _).smul h
  have he : ContDiffAt ℝ (↑n) Y 0 :=
    contDiffAt_pi.mpr fun i : Fin (n - 1) =>
      T _ (i.val + 2) (contDiffAt_infty.mp (varies h i.val |>.contDiffAt (x := (0 : ℝ))) n)
  have hp : ContDiffAt ℝ (↑n) (Q ∘ Y) 0 :=
    ContDiffAt.comp 0 (f := Y) (g := Q)
      (by
        rw [h0]
        exact
          contDiffAt_pi.mpr fun i => (((XSpace.peg H n).shot (K.looks i)).contDiffAt).of_le le_top)
      he
  have hz : (Q ∘ Y) 0 = 0 := by
    rw [comp_apply, h0]
    exact funext fun i => takes_zero ..
  have hy : Agree n 0 ((K.recover ∘ Q) ∘ Y) Y := by
    have hx : Agree n 0 K.recover f :=
      ⟨K.recover_smooth.contDiffAt.of_le le_top, hf, blockTaylor_jets hf⟩
    have hm : Tendsto Y (𝓝 0) (𝓝 0) := h0 ▸ he.continuousAt
    have hq : f ∘ (Q ∘ Y) =ᶠ[𝓝 0] Y := hm.eventually K.kit.2.2.1
    exact
      ((Agree.refl hp).comp
            (by
              rw [hz]
              exact hx)).trans
        (Agree.symm (Agree.of_event hq.symm he))
  rw [show (fun t : ℝ => reader K p.val (H.links n (records h t) t)) = R ∘ ((K.recover ∘ Q) ∘ Y) from
      funext fun x => by
        rw [scales H (records h x)]
        rfl]
  rw [show (fun t : ℝ => read (scaleJet (records h t) t) p.val) = R ∘ Y from ?_]
  exact hy.apply_smooth (snap_read_smooth n p.val _ |>.contDiffAt)
  exact funext fun x => (racts p (scaleJet (records h x) x)).symm

lemma radix_jet (K : XSpace.Survey G H n) (hp : v ∈ Grade (n, l)) (he : Matches A B n) (h : Flow B)
    (hh : ∀ i, ContDiff ℝ ∞ (A i)) :
    Agree n 0 (fun t => reader K v.val (coarse A t))
      (fun t : ℝ => t ^ n • read (records h 0) v.val) := by
  let f (t : ℝ) := read (records h t) v.val
  refine ((midpoint_read K v.val h hh he).trans ((columns_lift h K v).trans (book K h v))).trans ?_
  simp_rw [scales_here hp]
  have ht : ContDiffAt ℝ (↑n) f 0 := by
    rw [show f = (fun y : Snap G n => read (expand n y) v.val) ∘ (fun t => trunk n (records h t)) from
        ?_]
    swap
    · exact funext fun t => (racts ..).symm
    exact
      (snap_read_smooth n v.val _).contDiffAt.comp _
        (contDiffAt_pi.mpr fun i => contDiffAt_infty.mp ((varies h i.val).contDiffAt) n)
  refine
    power_agree (u := f) (v := fun t : ℝ => f 0) (k := 0) ht contDiffAt_const
      (Agree.line (ht.of_le (by simp)) contDiffAt_const ?_) (by omega)
  intro t ht
  simp only [show t = 0 by omega, iteratedDeriv_zero]
end jet
end YM.WilsonMS.Panel
