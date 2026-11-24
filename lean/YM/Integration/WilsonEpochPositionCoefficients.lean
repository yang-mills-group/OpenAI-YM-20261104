import YM.FVA2.Handoff
import YM.Integration.WilsonBookedSectionGerm
import YM.Integration.WilsonEpochCylinderDifference

/-! Compare the enrolled microscopic section with the actual finite epoch
which computes the booked position-scheme coefficients. The signed correction
is a specified insertion into their common interacting inversion quotient.
All placements, lower Wick terms and their individual Laurent shifts remain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochPositionCoefficients

open Function Lattice Source Source.Drops Labels Wilson PhysicalNext.Repeat.Legato
open XSpace FVA2 FVA2.Arrival FVA2.Register PertExtension
open WilsonEpochCylinderDifference
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)

/-- The transport used by the two independently selected data sets is
identical for all times, by uniqueness of the actual link ODE. -/
theorem holonomy (H K : Hol G) : H = K := by
  cases H with
  | mk f hf =>
    cases K with
    | mk g hg =>
      have eq : f = g := by
        funext d J h l
        exact (hf d J h l).unique (hg d J h l)
      subst g
      rfl

private theorem same_read {H : Hol G} {d : ℕ} (A : Survey G H d)
    (v : Label G d) (J : Jet G) (k : ℕ) (hk : k ≤ d) :
    iteratedDeriv k (fun h : ℝ => (R.family.localSection d).evaluate
      ((R.family.labels.level d).coords v) (R.family.params.links d J h)) 0 =
    iteratedDeriv k (fun h : ℝ => read (expand d (A.reading (H.links d J h))) v.val) 0 := by
  have eq := holonomy H R.family.params
  subst H
  exact WilsonBookedSectionGerm.matched R A v J k hk

/-- Literally the finite coefficient source used by the position solve,
tested before taking a limit or opening the terminal vacuum. -/
theorem chart (Y : Initialize G) (s : Folio G) (J : Jet G) (j : ℕ) (hj : j ≤ s.u.size) :
    iteratedDeriv j (fun h : ℝ => (R.family.localSection s.u.size).evaluate
      ((R.family.labels.level s.u.size).coords (s.item Y))
      (R.family.params.links s.u.size J h)) 0 =
    iteratedDeriv j (fun h : ℝ => Press.wheel (Y.surveys s.u.size) (s.item Y).val
      (Y.hol.links s.u.size J h)) 0 :=
  same_read R (Y.surveys _) (s.item Y) J j hj

def placed (Y : Initialize G) (n : Side) (s : Folio G) : Config G n → ℝ :=
  ActualStencilCylinder.observed (R.family.localSection s.u.size)
    ((R.family.labels.level s.u.size).coords (s.item Y)) n (wrap n s.addr)

theorem placed_valid (Y : Initialize G) (n : Side) (s : Folio G) :
    Orb.PreTest (placed R Y n s) :=
  ActualStencilOrb.observed_pretest _ (R.makes.sections _) _ _

/-- Both original fields have their actual complex phase, even after wrapping
the center and all stencil edges at this period. -/
theorem phase (Y : Initialize G) (n : Side) (s : Folio G) (U : Config G n) :
    (placed R Y n s U : ℂ) =
      (R.family.localSection s.u.size).places
        ((R.family.labels.level s.u.size).coords (s.item Y)) (wrap n s.addr) U ∧
    (Folio.placard Y s n U : ℂ) = Press.wheel (Y.surveys s.u.size)
      (s.item Y).val (expandAt (wrap n s.addr) U) := by
  refine ⟨?_,Folio.raw_claim Y s n U⟩
  let F := R.family.labels.level s.u.size
  let c := F.coords (s.item Y)
  have hv : realBar (s.item Y) = s.item Y := Subtype.ext (Folio.real Y s)
  have hc : star c = c := by
    funext i
    change star (F.coords (s.item Y) i) = _
    rw [← F.conj_basis,LinearEquiv.symm_apply_apply,hv]
  apply Complex.conj_eq_iff_re.mp
  change star ((R.family.localSection s.u.size).evaluate c _) =
    (R.family.localSection s.u.size).evaluate c _
  exact ((R.makes.sections s.u.size).ordinary_real c
    (expandAt (wrap n s.addr) U)).symm.trans
    (congrArg (fun x => (R.family.localSection s.u.size).evaluate x
      (expandAt (wrap n s.addr) U)) hc)

def actual (Y : Initialize G) (n : Side) (l : List (Folio G)) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => Orb.diag (Orb.restrictedO (word (placed R Y n) l)) (Folio.asset l + k))

def residual (Y : Initialize G) (n : Side) (l : List (Folio G)) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => Orb.diag (Orb.restrictedO
    (insertion (placed R Y n) (fun s => Folio.placard Y s n) l)) (Folio.asset l + k))

theorem closed (Y : Initialize G) (n : Side) (ev : Even n.val) (l : List (Folio G)) :
    actual R Y n l = Folio.coefficients Y n l + residual R Y n l := by
  have good : Orb.PreTest (word (placed R Y n) l) := by
    induction l with
    | nil => exact Folio.matured Y n [] ev
    | cons a l ih => exact FVA2.Change.pre_pair (placed_valid R Y n a) ih
  apply PowerSeries.ext
  intro k
  simp only [actual,residual,Folio.coefficients,FormalOPE.RG10.MultiGauge.Stack.drop,
    PowerSeries.coeff_mk,map_add]
  have hr := mixed ev (placed R Y n) (fun s => Folio.placard Y s n) l good
    (Folio.matured Y n l ev) (Folio.asset l + k)
  exact (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)

private theorem scan_plus {A : Type} [AddCommMonoid A] (p : List (Birth G))
    (f g : List (Folio G) → A) :
    Birth.scan p (fun l => f l + g l) = Birth.scan p f + Birth.scan p g := by
  induction p generalizing f g with
  | nil => rfl
  | cons a p ih =>
    rw [Birth.scan,Birth.scan,Birth.scan,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ =>
      ih (fun l => f (a.chooses j :: l)) (fun l => g (a.chooses j :: l))

/-- Every actual Wick subtraction term is included before the coefficient is
read. This equality is independent of the choice of a finite directory. -/
theorem assembled (Y : Initialize G) (n : Side) (ev : Even n.val) (p : List (Birth G)) :
    Birth.scan p (actual R Y n) = Birth.words Y n p + Birth.scan p (residual R Y n) := by
  have h := funext (closed R Y n ev)
  rw [h]
  exact scan_plus p _ _

/-- Exact numerical difference from the independently fixed epoch's own
normalized terminal Gaussian, including its full vacuum and the finite-order
reimbursement for every occurrence of every emitted Wick term. -/
theorem epoch (N : WilsonPrescription G) (i B : ℕ) (P : Handoff.Directory N i B)
    (p : List (Birth G)) (k : ℕ) (hk : Handoff.Directory.requested p + k ≤ B) :
    let n := (N.run.step i).p.side
    PowerSeries.coeff k (Birth.scan p (actual R N.scheme n)) - PowerSeries.coeff k (P.product p) =
      PowerSeries.coeff k (Birth.scan p (residual R N.scheme n)) := by
  intro n
  have ev : Even n.val := even_iff_two_dvd.mpr (N.run.step i).p.even
  have exactEpoch := P.scan_construct p k hk k le_rfl
  rw [WilsonPrescription.serial,Arrival.Episodic.sum_world] at exactEpoch
  rw [assembled R N.scheme n ev p,map_add,exactEpoch,add_sub_cancel_left]

end YM.Integration.WilsonEpochPositionCoefficients
end

