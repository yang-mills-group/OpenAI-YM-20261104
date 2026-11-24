import YM.Integration.WilsonMaxwellThermometerNominatedGroundPurse

/-! The true measured three-field panel has small proper residual relative to
its bounded Maxwell table, in the exact ordered regulator and radius filters.
Consequently only the signed six proper ordinary differences from the other
bank, on these same fields, need an order-one estimate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundPanel
open Finset Filter Function Set Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE OPE.Orbits Next.UVStress Climb Table Spec Extraction Trace Trace.Pilot PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose
open Marker QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerNominatedProperFaces WilsonMaxwellThermometerNominatedDelta
open WilsonMaxwellThermometerNominatedGroundPurse
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (A:ℝ→Group R.family 6)
  {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
  (simple:G.Simple) (hl:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A J)
local notation "J₀" => Stock.census (Fin 3)
abbrev Index:=ℝ×(ℕ×ℕ)
def actual (w:Index) (x:Points 3):Poly J₀:=table (WilsonPositionThermometerGradedReading.moment
  w.1 (WilsonPositionCorrectedCap.adjusted F J V A w.1) w.2 x)
local notation "P" => actual R F J V A
local notation "W" => policy R

include simple hl book in
theorem original (lead:Leading F J) {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3)
    {δ:ℝ} (small:0<δ):
    ∀ᶠw:Index in trail.curry (Y:Filter _),∀x∈E,rent (residue (P w x) (W x))≤δ:=by
  obtain ⟨B,one,covered⟩:=budget R compact legal
  have good:0<8*B:=by linarith
  filter_upwards [WilsonMaxwellThermometerNominatedProperFaces.original R F J V A simple hl book lead compact legal
    (δ/(8*B)) (div_pos small good)] with w paid x hx
  have six:=WilsonMaxwellThermometerNominatedDeltaProper.six (P w x) (W x) (δ/(8*B))
    (div_nonneg small.le good.le) ((WilsonMaxwellThermometerNominatedGroundPurse.unit _).trans (WilsonMaxwellThermometerNominatedGroundPurse.unit _).symm) (fun s non _=>by
      change ‖(if s=(J₀).quiet then (1:ℂ) else _) - (if s=(J₀).quiet then (1:ℂ) else _)‖≤_
      rw [if_neg non,if_neg non]
      exact (paid s.val x hx).le)
  have h:=WilsonMaxwellThermometerNominatedDeltaProper.spent (P w x) (W x) (W x) (WilsonMaxwellThermometerNominatedGroundPurse.unit _)
  rw [WilsonMaxwellThermometerNominatedDeltaProper.self (W x) (WilsonMaxwellThermometerNominatedGroundPurse.unit _),sub_zero] at h
  have non:0≤rent (inverseMass (W x)):=Poly.nonnegative (fun _:Fin 3=>zero_lt_one) _
  have pos:0≤8*(δ/(8*B)):=by positivity
  exact (h.trans (mul_le_mul six (covered x hx) non pos)).trans_eq (by field_simp)

include simple hl book in
theorem compared (lead:Leading F J) {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3)
    (x:Index→Points 3) (here:∀ᶠi in trail.curry (Y:Filter _),x i∈E)
    (Gears:Index→Poly J₀) (g:Index→ℝ) (C:ℝ) (cpos:0≤C)
    (gpos:∀ᶠi in trail.curry (Y:Filter _),0<g i)
    (g₀:Tendsto g (trail.curry (Y:Filter _)) (𝓝 0))
    (qu:∀ᶠi in trail.curry (Y:Filter _),(Gears i).part (J₀).quiet=1)
    (proper:∀ᶠi in trail.curry (Y:Filter _),∀s:(J₀).Mode,s≠(J₀).quiet→s≠WilsonThermometerCenteredAlgebra.full→
      ‖(P i (x i)).part s-(Gears i).part s‖≤C*g i):
    Tendsto (fun i=>‖discrepancy (P i (x i)) (Gears i) (W (x i))‖/g i) (trail.curry (Y:Filter _)) (𝓝 0):=by
  obtain ⟨B,one,covered⟩:=budget R compact legal
  refine WilsonMaxwellThermometerNominatedDelta.small _ _ _ _ _ (8*C*B) ?_ gpos g₀ ?_ ?_
  · filter_upwards [qu] with i qi using ⟨WilsonMaxwellThermometerNominatedGroundPurse.unit _,qi,WilsonMaxwellThermometerNominatedGroundPurse.unit _⟩
  · apply Metric.tendsto_nhds.mpr
    intro t ht
    filter_upwards [here,original R F J V A simple hl book lead compact legal (half_pos ht)] with i hx paid
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (show 0≤rent (residue (P i (x i)) (W (x i))) from Poly.nonnegative (fun _:Fin 3=>zero_lt_one) _)]
    exact (paid (x i) hx).trans_lt (half_lt_self ht)
  · filter_upwards [here,proper,gpos,qu] with i hx P₀ g₁ G₁
    have six:=WilsonMaxwellThermometerNominatedDeltaProper.six (P i (x i)) (Gears i) _ (mul_nonneg cpos g₁.le) ((WilsonMaxwellThermometerNominatedGroundPurse.unit _).trans G₁.symm) P₀
    have h:=WilsonMaxwellThermometerNominatedDeltaProper.spent (P i (x i)) (Gears i) (W (x i)) (WilsonMaxwellThermometerNominatedGroundPurse.unit _)
    have p:0≤rent (inverseMass (W (x i))):=Poly.nonnegative (fun _:Fin 3=>zero_lt_one) _
    exact (h.trans (mul_le_mul six (covered _ hx) p (mul_nonneg (by norm_num) (mul_nonneg cpos g₁.le)))).trans_eq (by ring)

end YM.Integration.WilsonMaxwellThermometerNominatedGroundPanel
