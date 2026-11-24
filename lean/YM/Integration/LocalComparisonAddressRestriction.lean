import YM.Integration.LocalComparisonPackets
import YM.Integration.LocalComparisonFunctionalRetains

/-!
# Restricting insertion addresses without changing full packets or rows

The address argument is a lower support requirement. Restricting it does not
change any token plot, path, reader, coefficient, countable root payment or
cover bound. The same restriction preserves the original complete Taste rows.
The singleton specializations use the original origins and their existing
membership receipts; no new input, representative or denominator is chosen.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

open Lattice Wilson RG Marker
open RG3.Held RG3.Forms RG3.Script.Picnic

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}

namespace MarkedPackets.Paid

variable {D : V → ComparisonDensity.Address.Orbit}
    {P : MarkedPackets D G n R} {p : BudgetPoint}
    {address smaller : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- Restrict only the insertion-address requirement in the same full payment. -/
theorem restrict_addresses
    (h : P.Paid p address region w g width budget coverOffset coverSlope)
    (hsub : ∀ v, smaller v ⊆ address v) :
    P.Paid p smaller region w g width budget coverOffset coverSlope where
  width_pos := h.width_pos
  positive := h.positive
  coefficient := h.coefficient
  paths := h.paths
  addresses i T hi v hv := (hsub v).trans (h.addresses i T hi v hv)
  symmetry := h.symmetry
  reads := h.reads
  multilinear := h.multilinear
  roots := h.roots
  cover := h.cover
  width_reserved := h.width_reserved

/-- The original origins suffice as lower insertion addresses; full token
plots and every original payment are retained. -/
theorem singleton_addresses
    (h : P.Paid p address region w g width budget coverOffset coverSlope)
    (o : V → Site n) (horigin : ∀ v, o v ∈ address v) :
    P.Paid p (fun v => {o v}) region w g width budget coverOffset coverSlope :=
  restrict_addresses h fun v z hz => by
    have he : z = o v := Finset.mem_singleton.mp hz
    subst z
    exact horigin v

end MarkedPackets.Paid

namespace FunctionalRetains

variable {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {address smaller : V → Support n}

/-- Restrict only the address required of each nonzero whole functional. -/
theorem restrict_addresses (h : FunctionalRetains T address)
    (hsub : ∀ v, smaller v ⊆ address v)
    (horigin : ∀ v, o v ∈ smaller v) :
    FunctionalRetains T smaller where
  origins := horigin
  regular i v hn hv := (hsub v).trans (h.regular i v hn hv)
  forced i j v hn hv := (hsub v).trans (h.forced i j v hn hv)
  captions i v hn hv := (hsub v).trans (h.captions i v hn hv)

/-- The same complete Taste retains its original singleton origins. -/
theorem singleton_addresses (h : FunctionalRetains T address) :
    FunctionalRetains T (fun v => {o v}) :=
  restrict_addresses h
    (fun v z hz => by
      have he : z = o v := Finset.mem_singleton.mp hz
      subst z
      exact h.origins v)
    (fun v => Finset.mem_singleton_self (o v))

end FunctionalRetains

end YM.Integration.LocalComparison
