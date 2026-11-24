import YM.FVA2.Removal.Dance
import YM.FVA2.Generator.Cycle
import YM.FVA2.Register.Pressroom
/-!
# Regulator-removal estimates before imposing a relation between period and spacing

Note the (eventual) rates in two-term form below. No growth/bigness of total
side required to have the estimates in this form. Need **all** geometric/data
hypotheses as in `Fit` (on offsets, positioning & clearance etc.). See also
`YM/FVA2/Notch/Platter` for a variant on `Spots` geometries. Use in particular
the mass convention `T.profile.η i = μ - θ i` at the fixed `μ` (= log ν). See
`Teller/Mass`. Even with `Fit` no smallness/convergence is claimed here without
some suitable additional condition e.g. super-polynomial growth of side
(see `Main.Match` for related eventuality and estimates where $a→0$ on such a path).

`phys` = physical side length (one-dimensional), not four-volume.
For the internal kernel/differentiated estimates in `MenuCost`, see `Wires`;
`power_run` points out the **volume** cost is sufficient here for the change
in ordinary-product arrays from the source-dependent canonical undo. These
results are only on the *formal-to-formal* comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Latch MS.Latch.Job MS.Tide MS.High
open MS.Vane MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.Fleet MS.Dial
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Swirl
open Register WilsonPrescription
open scoped Topology ContDiff Interval
variable {I:Type} {l:Filter I} {P:Geo I}{L:I→Side}{V: MS.Vista.Visa I}{μ:ℝ}{F:I→ℂ}
variable {W:Type}[LinearOrder W]
open PeakT (ordZ)
lemma Vol.hard
      (p:Vol l P L F)
      : ∃ C:ℝ,0<C∧∃ m:ℕ,
      ∀ᶠ i in l, ‖F i‖ ≤ C*( ((exp (-P.θ i))^m)⁻¹*( phys P L i )^(-mildG) )
      := by
 obtain ⟨C,hC,m,H⟩:= p; refine ⟨ C,hC,m,H.mono fun i hi=>?_⟩; rw [ exp_neg, inv_pow,inv_inv, ← exp_nat_mul ]; exact hi.trans (mul_le_mul_of_nonneg_left ( toPhysical .. ) hC.le)
lemma Total.hard
      (p:Total l P L F)
      : ∃ C:ℝ,0<C∧∃ m:ℕ,
      ∀ᶠ i in l, ‖F i‖ ≤ C*((exp (-P.θ i))^ mildG + ((exp (-P.θ i))^m)⁻¹*( phys P L i )^(-mildG) )
      := by
 obtain ⟨C,hC,m,H⟩:= p; refine ⟨ C,hC,m,H.mono fun i hi=>?_⟩; rw [ ← exp_mul, exp_neg ( P.θ i ), inv_pow,inv_inv, ← exp_nat_mul ]; apply hi.trans; apply mul_le_mul_of_nonneg_left _ hC.le; apply add_le_add _ ( toPhysical .. ); unfold lake; apply exp_monotone; linarith only []
variable {G:Gauge} (N: WilsonPrescription G){S:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
variable {A:Land.Prescription (Press.portDeck G)} (u : W→Label (Press.portDeck G)) (g:G.Simple) (h:Posted N S A)
-- `comap`: only require eventual after a theta threshold.
-- $D^a(0)$ etc are captured separately. Use an arbitrary trial.
variable (T:Trial I W)
include g h
lemma all_requests (v:ℝ)
      (H:Fit T v)
      : ∃! p: (Terrify W I)×(Terrify W I),
      MenuCost S N.scheme T A u v ( Filter.comap T.profile.θ atTop ) p.1 p.2 := by
 obtain ⟨f,z,hX⟩:= tabulate S N.scheme T A u H tendsto_comap h.born.Taylor g; refine ⟨ ( f,z ),hX,fun y hy=>?_⟩; obtain ⟨Y,U,D,E,G,H,V,hF,hD,hE⟩:= hX.fabric; obtain ⟨ F,B,C,Q,R,hP,hQ,h₁,h₂,H'⟩:= MenuCost.fabric ( show MenuCost S N.scheme T A u v _ y.1 y.2 from hy ); exact Prod.ext ( Fleet.orb_unique h₁ hF ) (Fleet.orb_unique h₂ hD)
-- Or any finer filter `l` (log spacing coordinate goes to atTop).
variable (v:ℝ)(h₀:Fit T v)(hx:Tendsto T.profile.θ l atTop)
include h₀ hx
lemma power_run : ∃ f z: Terrify W I,
      MenuCost S N.scheme T A u v l f z
      ∧ ∀ (s:Finset W)(k:ℕ),
      Vol l T.profile T.side (fare (Label.h∘u) T.profile (ordZ f) s k -
        fare (Label.h∘u) T.profile (ordZ z) s k) := by
 obtain ⟨ f,z,hX ⟩:= tabulate S N.scheme T A u h₀ hx h.born.Taylor g; exact ⟨ f,z,hX,fun s k=> ( hX.full h₀ s k ).volume ⟩
end YM.FVA2.Removal
