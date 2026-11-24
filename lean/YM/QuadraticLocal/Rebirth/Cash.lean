import YM.QuadraticLocal.Rebirth.Balance
import YM.QuadraticLocal.Earn.Blend
/-!
# Functional specifications for receiving the birth of marks

 Issued even on moving stage and all Γ-provider opportunities. Missing Real g,
 gc assurances? those are treated separately after all costs. `Recharged` in fine units;
 term distribution along each stipend Part.Meta.Em.Action; can't clone without the
 legal Loan (t and scale). Prices are *scalar* budget, recast with masks in proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Chart QuadraticLocal.Sunrise

variable (Q:Pace.Coin)(h : Q 0=0)(g d:ℝ) -- before & after
variable (L j u:ℕ)(a ν z:ℝ)

-- Price model estimates duplicated offset at each talent.Old order `j` not `nCoarse > j`.
structure Recharged : Prop where
   nice : j ≤ L
   quota : 1 ≤ a
   attendance : (j+1:ℕ)* a ≤ z -- coerces reals; not ζ SupportExponent!
   progress (p:Loan)(hp:p.e≤ j)(hq:p.toll ≤ u): ∀ i:ℕ, i≤ j-p.e → 1+|tariff Q h L p.lag i| ≤ a
   earns (p:Loan)(hp:p.e≤ j)(hq:p.toll ≤ u): |g^p.e*(Balance.balance Q h L p.lag g d (j-p.e))| ≤ ν
namespace Recharged
lemma value_shift (Q':Pace.Coin)(h':Q' 0=0)(e:Q=Q')(s:ℤ) : Balance.balance Q h L s g d j=Balance.balance Q' h' L s g d j:= by cases e; rfl
variable {Q h L j u a ν z g d}(H: Recharged Q h g d L j u a ν z)
include H
lemma z_quota : 1≤ z:= le_trans (one_le_mul_of_one_le_of_one_le (by norm_cast; omega) H.quota) H.attendance
-- Positive ν follows from the calendar separately (e.g. when no marks to compare).* No erroneously deriving it without checking `u≥1`.
end Recharged
end YM.QuadraticLocal.Rebirth
