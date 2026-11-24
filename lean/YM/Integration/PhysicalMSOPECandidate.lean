import YM.Integration.EngineeringWholeHorizon
import YM.Integration.PhysicalMSOPEInput
import YM.RG11Proof.Neighborhood.Hearts

/-!
The full-horizon candidate in the actual physical frame.

The comparison applies the inverse of the same complete frame through the
chosen horizon. Its comparison vector is the finite truncation
of the native formal expression Z⁻¹ C(f; Z inputs), evaluated at relative
radius one.  Only this finite polynomial is evaluated at the real coupling;
the formal coupling and field changes are not numerically realized.

The candidate's detector readout is proved exactly.  No identification of
an arbitrary OPE atlas with the independent MS prescription, and no estimate
for the weighted complete-product residual, is assumed or asserted here.
Identifying the supplied J and coupling with the exact position-normalized
H and g is also separate; `Leading` alone does not do so.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.PhysicalMSOPECandidate
open Function Filter Set Spec OPE OPE.Orbits PhysMS
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open EngineeringWeightedReadout PhysicalMSOPEReadout
open scoped Topology BigOperators Classical

section Formal
variable {G : Gauge} {L : Labels.Frames G} {n i D : ℕ}

/-- The literal coefficient of a native OPE block on arbitrary input fields,
using the one canonical free basis at each horizon. -/
def blockCoefficient (B : Blocks L n i D) (s : ℝ)
    (v : Fin n → E L i) (k : ℕ) : E L D :=
  ∑ u : sheaf L n i,
    (∏ a : Fin n, (RG11.Fields.tower L i).b.repr (v a) (u a)) •
      ∑ j : lab L D,
        PowerSeries.coeff k (B s u j) • (RG11.Fields.tower L D).b j

/-- Finite evaluation after all formal operations have been performed. -/
def blockTruncation (B : Blocks L n i D) (s : ℝ)
    (v : Fin n → E L i) (N : ℕ) (t : ℝ) : E L D :=
  ∑ k ∈ Finset.range (N + 1), (t : ℂ) ^ k • blockCoefficient B s v k

theorem blockCoefficient_congr (B B' : Blocks L n i D) (s : ℝ)
    (v : Fin n → E L i) (k : ℕ)
    (h : ∀ u j, PowerSeries.coeff k (B s u j) = PowerSeries.coeff k (B' s u j)) :
    blockCoefficient B s v k = blockCoefficient B' s v k := by
  simp only [blockCoefficient, h]

/-- Only the declared coefficient prefix is used; higher orders cannot
change a finite candidate. -/
theorem blockTruncation_congr (B B' : Blocks L n i D) (s : ℝ)
    (v : Fin n → E L i) (N : ℕ) (t : ℝ)
    (h : ∀ k ≤ N, ∀ u j,
      PowerSeries.coeff k (B s u j) = PowerSeries.coeff k (B' s u j)) :
    blockTruncation B s v N t = blockTruncation B' s v N t := by
  unfold blockTruncation
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun w : E L D => (t : ℂ) ^ k • w)
    (blockCoefficient_congr B B' s v k
      (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))

/-- Native `crown` is exactly input conversion, coupling substitution and
inverse output conversion, in that order.  Its scale argument zero means
relative radius one.  The same formal p/Z are used at every order. -/
def composedTruncation (p : PowerSeries ℝ)
    (Z : ∀ d, RG11.Window.SquareAt L d) (B : Blocks L n i D)
    (v : Fin n → E L i) (N : ℕ) (t : ℝ) : E L D :=
  blockTruncation (crown p Z B) 0 v N t

/-- A fixed anchored coupling conversion preserves the declared coefficient
prefix, including both finite field-matrix operations. -/
theorem composedTruncation_congr (p : PowerSeries ℝ) (hp : RG11.Jets.Anchored p)
    (Z : ∀ d, RG11.Window.SquareAt L d) (B B' : Blocks L n i D)
    (v : Fin n → E L i) (N : ℕ) (t : ℝ)
    (h : RG11.Jets.MatThrough N (B 0) (B' 0)) :
    composedTruncation p Z B v N t = composedTruncation p Z B' v N t := by
  have hs := h.subs (RG11.Jets.Through.refl (RG11.Jets.deposit p))
    (RG11.Jets.deposit_base p hp)
  have hc : RG11.Jets.MatThrough N ((crown p Z B) 0) ((crown p Z B') 0) :=
    ((RG11.Jets.MatThrough.refl (castNet (Z i) n)).mul hs).mul
      (RG11.Jets.MatThrough.refl (fieldInv (Z D)))
  exact blockTruncation_congr _ _ 0 v N t (fun k hk u j => hc u j k hk)

/-- The native uniqueness theorem for genuine OPE blocks makes the finite
converted field independent of the particular such block presented. -/
theorem composedTruncation_eq_of_snug (p : PowerSeries ℝ)
    (hp : RG11.Jets.Anchored p) (Z : ∀ d, RG11.Window.SquareAt L d)
    (A : ShapeReport G L) (u : Design n) (c : E4) (N : ℕ)
    {δ δ' : ℝ} {B B' : Blocks L n i D}
    (hB : Snug A u c N δ B) (hB' : Snug A u c N δ' B')
    (v : Fin n → E L i) (t : ℝ) :
    composedTruncation p Z B v N t = composedTruncation p Z B' v N t :=
  composedTruncation_congr p hp Z B B' v N t (Snug.vision hB hB' 0)

/-- Increasing the requested perturbative order adds exactly its next
coefficient; no new prescription or conversion is selected. -/
theorem composedTruncation_succ (p : PowerSeries ℝ)
    (Z : ∀ d, RG11.Window.SquareAt L d) (B : Blocks L n i D)
    (v : Fin n → E L i) (N : ℕ) (t : ℝ) :
    composedTruncation p Z B v (N + 1) t =
      composedTruncation p Z B v N t +
        (t : ℂ) ^ (N + 1) • blockCoefficient (crown p Z B) 0 v (N + 1) := by
  exact Finset.sum_range_succ _ _
end Formal

section Physical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) {n i D : ℕ} (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (v : Fin n → E C.labels i)

/-- The declared formal comparison is placed in the existing physical frame,
with no additional Family, Final, basis or scale selection. -/
def candidate (N : ℕ) (t r : ℝ) : S.Field D :=
  J r D (composedTruncation p Z B v N t)

/-- The complete inverse frame cancels literally on this candidate. -/
theorem candidate_readout (N : ℕ) (t r : ℝ) :
    wholeReadout U J r
      (fun a => witnessAt S D (U.listen a) (candidate J p Z B v N t r)) =
        composedTruncation p Z B v N t :=
  wholeReadout_frame U J r _

/-- The original full Reader packet in the same running frame. -/
def actualOutput (r : ℝ) (x : Fin n → E4) : E C.labels D :=
  (J r D).symm (R.packet D x (Frame.born J r v) 0)

/-- The still-to-be-paid complete-product/MS error, in the original full
output norm. The actual samples use the original fixed detector exteriors. -/
def weightedMSResidual (N : ℕ) (t r : ℝ) (x : Fin n → E4) : E C.labels D :=
  wholeReadout U J r
    (candidateResidual J U v r x (candidate J p Z B v N t r))

/-- Exact full-horizon split. The ordinary OPE term has the separate native
positive-length-power estimate; this identity does not estimate the second
term or assume any commutation with homogeneous Reader cuts. -/
theorem exact_split (N : ℕ) (t r : ℝ) (x : Fin n → E4) :
    actualOutput F R J v r x - composedTruncation p Z B v N t =
      weightedMSResidual J U p Z B v N t r x -
        wholeReadout U J r (detectorOPEError F R J v U r x) := by
  change (J r D).symm (R.packet D x (Frame.born J r v) 0) -
    composedTruncation p Z B v N t = _
  rw [← wholeReadout_field U J r (R.packet D x (Frame.born J r v) 0),
    ← candidate_readout J U p Z B v N t r]
  change wholeReadout U J r _ - wholeReadout U J r _ =
    wholeReadout U J r _ - wholeReadout U J r _
  rw [← map_sub, ← map_sub]
  apply congrArg (wholeReadout U J r)
  ext a
  simp only [Pi.sub_apply, candidateResidual, detectorOPEError]
  ring

end Physical
end YM.Integration.PhysicalMSOPECandidate
