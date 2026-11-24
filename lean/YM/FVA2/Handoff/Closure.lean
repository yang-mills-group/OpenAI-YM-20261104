import YM.FVA2.Embr.Provider

/-!
# Closing the `Fk` open conditional of our Wilson prescription

Bridge for use also by analytic comparison. Rigorous finite-order reconstruction. Suppose one is
working with the `Puffs` exported realization of the trajectory (Haar, tag conventions,
conditional frames, and **proof** of the steady/tag data at each retained field).
It exists, with all those proofs; `Directory.always`. Then:

* `mask_fk` gives the output weight as a power series; strip the position-dependent
  overhead from `Fk.birth`, and put the terminal chart tissue in exactly once.
* `mark_fk` uses `Fk.read` (uses the **full conditional denominator** already!)
  on the **whole joint product** and keeps the prescribed Laurent charge.
* Take the terminal Gaussian coefficient averages (`integrates`) and divide by a
  **common** vacuum series.

These formulas give exactly the normalized source diagrams through the requested order,
including on the positive-mark sector (choose the physical entries from `Arrival.Birth`,
keep all the W pieces and powers etc.). See `construction`, `scan_construct`. No convergence assumptions or bounds
on the size of the `Fk` data: the functions of the open field *as read off with these
participants and corrections* are proved polynomial (orders in range), not assumed
well-behaved. E.g., see `Directory.marked_polynomial`. Don't use
terms of higher order than requested by the
`Directory` (allow for Laurent shift too; see `construction`, `scan_construct`; definitions of functions aren't
truncated by syntax).
There's no suggestion analytic costs are under control for a UV estimate: all the proofs about `Fk`
here are for each fixed geometry/epoch and at fixed orders. No extension to an actual density
or measure estimate intended by `mask_fk`, `mark_fk`. Nor using any MS hypothesis!

Compare also `Arrival.Episodic.candle` computing the same formula but directly with RG10
transfer (explicitly has the **later** terminal common vacuum division). For multi-mark packages
of log-connected words via `Route.Bulk`, see `YM/FVA2/Embr/{Packet,Provider}`.
For the needed stepwise and pre-conditional-denominator identities/
appearance of full open field see `YM/FVA2/{Embr/Signal,Hearth/Route}` and imports.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Handoff
open Function Filter Set FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open MeasureTheory PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking
open Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth RGComparison.Core16 Lumen
open Arrival
open Register Embr
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} (N : WilsonPrescription G) (i : ℕ)

-- shorthand for projections below
set_option quotPrecheck false
local notation "T" => (N.chooses i).T
local notation "top" => (N.run.step i).p.side
local notation "K" => (N.chooses i).clock
local notation "z" => (N.chooses i).clock.loops
local notation "priced" => (N.chooses i).clock.priced
local notation "HJ" => N.analyticChart
local notation "c" => collared T z HJ priced

abbrev Retained := Flats G (Bottom (FabricOf N i))
abbrev Terminal := Field (Cloth.choose (finish (N.chooses i).T))
local notation "lifting" => castAt (finish T)

/-- `M` is the requested *total* order, including the Laurent reimbursement on the
mixed physical entries. Use only coefficients up to that notice. Vary `place` freely (it's a
layout in `Embr.home` here, not the physical placement of the stencils!). -/
structure Directory (M : ℕ) where
    flag : G.ColorIndex
    shelf : Retained N i → Lumen.Shelf G Unit (Warm T)
    check (y : Retained N i) : Provision.Puffs N i flag y M (shelf y)
    place : Warm T → Site top

namespace Directory

lemma always (h : G.Simple) (M : ℕ) : Nonempty (Directory N i M) := by
  obtain ⟨s⟩ := Hearth.occupied h
  exact ⟨ ⟨ s, fun y => Exists.choose (Provision.issues N i s y M),
                fun y => Exists.choose_spec (Provision.issues N i s y M), fun _=>0 ⟩ ⟩

variable {N i} {M : ℕ} (D : Directory N i M)
abbrev σ (y : Retained N i) := Embr.home T (Gear.sheets K M) y D.flag (D.shelf y) D.place
def income_fk (y : Retained N i) : PowerSeries ℝ := PowerSeries.mk (Fk.birth (D.σ y) N.chart)
def mark_fk (l : List (Folio G)) (y : Retained N i) : PowerSeries ℝ :=
    PowerSeries.mk (Fk.read (D.σ y) N.chart (tease T D.flag)
      (lens T y D.flag (Hearth.rad T (Folio.scenario N.scheme top l))) (Folio.asset l))

def mask_fk (x : Terminal N i) : PowerSeries ℝ :=
    PowerSeries.C ((overheadC T z priced (lifting x) N.chart)⁻¹) * D.income_fk (lifting x)
      * Stack.read x (tissue N.chart (finish T).choose.Bulk)

def marked_fk (l : List (Folio G)) (x : Terminal N i) : PowerSeries ℝ :=
    D.mask_fk x * D.mark_fk l (lifting x)

local notation "travel" => Facade.drive T (z ∘ some) (Facade.headquarters z)
lemma mask_eq (y : Retained N i) : Through M
    (PowerSeries.C ((overheadC T z priced y N.chart)⁻¹) * D.income_fk y)
    (Stack.read y (travel 1 N.chart c).1.W) := by
    let a := overheadC T z priced y N.chart
    refine ((Through.refl (PowerSeries.C (R:=ℝ) a⁻¹)).mul ((D.check y).income D.place 1)).trans ?_
    have he : 0 < a := high_pos T z HJ priced y
    rw [← mul_assoc, ← _root_.map_mul, inv_mul_cancel₀ he.ne', map_one, one_mul]
    exact Through.refl _
lemma mask_through (x : Terminal N i) : Through M (D.mask_fk x)
    (Stack.read x (Hearth.flat T z priced HJ 1)) := by
    unfold mask_fk Hearth.flat; rw [_root_.map_mul, caught]
    exact (D.mask_eq (lifting x)).mul (Through.refl _)

variable (l : List (Folio G))
local notation "Ticket₀" => markValue N.scheme l top
lemma marks_through (U : ℕ) (h : Folio.asset l + U ≤ M) (y : Retained N i) : Through U
    (D.mark_fk l y) (Stack.read y (travel Ticket₀ N.chart c).2) := by
    intro j hj
    rw [mark_fk, PowerSeries.coeff_mk]
    exact ((D.check y).points l j ((Nat.add_le_add_left hj _).trans h) D.place).2
lemma marked_through (U : ℕ) (h : Folio.asset l + U ≤ M) (x : Terminal N i) : Through U
    (D.marked_fk l x) (Stack.read x (Hearth.flat T z priced HJ 1 *
      Hearth.current T z priced HJ Ticket₀)) := by
    unfold marked_fk Hearth.current; rw [_root_.map_mul, caught]
    exact ((D.mask_through x).mono (by omega)).mul (D.marks_through l U h (lifting x))

section Average
variable (N i)
local notation "μ" => tangent G (Loom.Truss.Bulk ( Cloth.choose (finish T) ))
local notation "q" => quiet T z priced HJ 1
/-- Gaussian on the terminal tree field; no claim of bounds on these as the regulator varies! -/
abbrev integrates (p : Terminal N i → PowerSeries ℝ) : PowerSeries ℝ :=
    PowerSeries.mk (fun k => (quiet T z priced HJ 1).average μ (fun x => PowerSeries.coeff k (p x)))
private lemma trace {k : ℕ} (A : Ticket (Terminal N i)) (p : Terminal N i → PowerSeries ℝ)
    (he : ∀ x, PowerSeries.coeff k (p x) = PowerSeries.coeff k (Stack.read x A)) :
    (fun x => PowerSeries.coeff k (p x)) = (PowerSeries.coeff k A).val := by
    ext1 x; rw [he, Stack.reading_term]
private lemma ingests {U : ℕ} (A : Ticket (Terminal N i)) (p : Terminal N i → PowerSeries ℝ)
    (he : ∀ x, Through U (p x) (Stack.read x A)) : Through U (integrates N i p) (input q μ A) := by
    intro k hk; rw [integrates, PowerSeries.coeff_mk, trace N i A p (fun x=> he x k hk)]
    unfold input throughPrice; rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk,PowerSeries.coeff_mk]; rfl
end Average
-- denominator/numerator fit even within `Through M` computations: applying `PowerSeries.trunc` also works
local notation "μ" => tangent G (Loom.Truss.Bulk (Cloth.choose (finish T)))
local notation "q" => Hearth.quiet T z priced HJ 1
local notation "vac₀" => Hearth.vacuum T z priced HJ
abbrev vacuum_fk := integrates N i D.mask_fk
abbrev numerator_fk := integrates N i (D.marked_fk l)
abbrev answer := D.numerator_fk l * D.vacuum_fk⁻¹

lemma unmarked_polynomial (k : ℕ) (h : k ≤ M) :
    (fun x => PowerSeries.coeff k (D.mask_fk x)) ∈ papers (Terminal N i) := by
    rw [trace N i _ _ (fun x => D.mask_through x k h)]
    exact Subtype.property _
lemma unmarked_integrable (k : ℕ) (h : k ≤ M) : Integrable
    ((fun x => PowerSeries.coeff k (D.mask_fk x))*(Hearth.quiet T z priced HJ 1).kern) μ :=
  useful μ q ⟨_,D.unmarked_polynomial k h⟩
lemma marked_polynomial (k : ℕ) (h : Folio.asset l + k ≤ M) :
    (fun x => PowerSeries.coeff k (D.marked_fk l x)) ∈ papers (Terminal N i) := by
    rw [trace N i _ _ (fun x => D.marked_through l k h x k le_rfl)]
    exact Subtype.property _
lemma marked_integrable (k : ℕ) (h : Folio.asset l + k ≤ M) : Integrable
    ((fun x => PowerSeries.coeff k (D.marked_fk l x))*(Hearth.quiet T z priced HJ 1).kern) μ :=
  useful μ q ⟨_,D.marked_polynomial l k h⟩

lemma denominator : Through M D.vacuum_fk vac₀ := ingests N i _ _ D.mask_through
@[simp] lemma vac_fk_zero : PowerSeries.constantCoeff D.vacuum_fk=1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, D.denominator 0 (Nat.zero_le _),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, Hearth.vacuum_ok]
lemma numerator (U : ℕ) (h : Folio.asset l + U ≤ M) :
    Through U (D.numerator_fk l) (Hearth.tally T z priced HJ Ticket₀) :=
    ingests N i _ _ (D.marked_through l U h)

/-- Closing to the **same** Wilson diagram through all announced orders. -/
theorem construction (U : ℕ) (h : Folio.asset l + U ≤ M) :
    Through U (D.answer l) (Folio.coefficients N.scheme top l) := by
    rw [← Arrival.Episodic.candle_eq N.scheme (N.chooses i) HJ]
    apply (D.numerator l U h).mul
    apply Through.invAlready (D.denominator.mono (by omega))
        (PowerSeries.mul_inv_cancel _ (ne_of_eq_of_ne D.vac_fk_zero one_ne_zero))
        (PowerSeries.mul_inv_cancel _ (by rw [Hearth.vacuum_ok]; exact one_ne_zero))
/-- Enough `Directory` budget: upper bound *all* the needed Laurent shifts,
    using only the tuple's slot counts (not physical position). -/
def requested : List (Arrival.Birth G) → ℕ :=
    fun b=> (b.map (fun v=> v.glyph.grade)).sum
private lemma scan_eq (p : List (Arrival.Birth G)) (U r : ℕ)
    (f g : List (Arrival.Folio G) → PowerSeries ℝ)
    (h : ∀ l, Folio.asset l ≤ r → Through U (f l) (g l))
    (he : requested p ≤ r) : Through U (Arrival.Birth.scan p f) (Arrival.Birth.scan p g) := by
    induction p generalizing f g r with
    | nil => exact h [] (Nat.zero_le _)
    | cons i p ih =>
        rw [Arrival.Birth.scan, Arrival.Birth.scan]; apply sumThrough; intro j _
        refine ih (requested p) (fun l=> f ((i.chooses j)::l)) (fun l=> g ((i.chooses j)::l)) (fun l H=>?_ ) le_rfl
        apply h; apply le_trans ( Nat.add_le_add (MS.Menus.Glyph.gallery_floor i.glyph j) H ) he
def product (p : List (Arrival.Birth G)) : PowerSeries ℝ:= Arrival.Birth.scan p D.answer
theorem scan_construct (p : List (Arrival.Birth G)) (U : ℕ) (h : requested p + U ≤ M) :
    Through U (D.product p) (N.serial i p) := by
    unfold product WilsonPrescription.serial
    rw [Arrival.Episodic.sum_world]
    exact scan_eq p U (requested p) _ _ (fun l he=> Directory.construction D l U ((Nat.add_le_add_right he _).trans h))
      le_rfl
end Directory
end YM.FVA2.Handoff
