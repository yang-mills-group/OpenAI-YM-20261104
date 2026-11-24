import YM.Integration.WilsonReporterWeightedDeployment
import YM.TraceExtension.Prom.Orion.Suds

/-! Remove the expanded marked radius in the actual normalized ordinary physical
moment. Both free and physical moments retain their identical labelled slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedOrdinary
open Lattice Wilson RG Source Cells Extraction Marker Next.Rank Perch Atlas Edition Station
     PhysicalNext.InteractingRank Market
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) {n k N p : ℕ} {d : Fin n → ℕ} {b : ℝ}
    {x : Points n}

def stretch (a : Fin n → ℝ) (v : (i : Fin n) → C.label (d i)) (i : Fin n) : C.label (d i) :=
  (a i : ℂ) • v i

theorem physical (a : Fin n → ℝ) (v : (i : Fin n) → C.label (d i))
    (j : Fin n → Site (C.side N p)) :
    C.numeric N p (q_asked (C:=C) (stretch C a v)) j =
      ((∏ i, a i : ℝ) : ℂ) * C.numeric N p (q_asked (C:=C) v) j := by
  change (C.ensemble d j) (fun i => (a i : ℂ) • v i) = _
  rw [MultilinearMap.map_smul_univ, Complex.ofReal_prod]
  rfl

theorem gaussian (a : Fin n → ℝ) (w : (i : Fin n) → C.label (d i)) (y : Points n) :
    (standard C).useAt (standard C) y (jointX (stretch C a w)) =
      ((∏ i, a i : ℝ) : ℂ) * (standard C).useAt (standard C) y (jointX w) := by
  change ((standard C).classMoment (standard C) d y)
    (fun i => (standard C).project _ ((a i : ℂ) • w i)) = _
  have law (i : Fin n) : (standard C).project (d i) ((a i : ℂ) • w i) =
      (a i : ℂ) • (standard C).project (d i) (w i) := ((standard C).project (d i)).map_smul _ _
  simp_rw [law]
  rw [MultilinearMap.map_smul_univ, Complex.ofReal_prod]
  rfl

theorem profile (a : Fin n → ℝ) (w : (i : Fin n) → C.label (d i)) (y : Points n)
    (s : Glyph.modes (Fin n)) :
    (Read.maxProfile C y (jointX (stretch C a w))).part s =
      ((∏ i, a ((Read.project s i).val) : ℝ) : ℂ) * (Read.maxProfile C y (jointX w)).part s := by
  exact gaussian (d:=fun i => d ((Read.project s i).val)) C
    (fun i=>a ((Read.project s i).val)) (fun i=>w ((Read.project s i).val)) (Read.portion s y)

theorem price (a : Fin n → ℝ) (w : (i : Fin n) → C.label (d i)) (y : Points n)
    (h : ∀ s : Glyph.modes (Fin n), (∏ i, a ((Read.project s i).val)) ≠ 1 →
      (Read.maxProfile C y (jointX w)).part s = 0) :
    Read.maxProfile C y (jointX (stretch C a w)) = Read.maxProfile C y (jointX w) := by
  funext s
  change (Read.maxProfile _ _ _).part s = (Read.maxProfile _ _ _).part s
  rw [profile]
  by_cases e : (∏ i, a ((Read.project s i).val)) = 1
  · simp [e]
  · rw [h s e, mul_zero]

theorem original (hc : C.Makes) {u : ℕ} (hN : k≤N) (fit : FitSky C.path.levels b k x)
    (a : Fin n → ℝ) (ha : ∀ i, 0<a i) (w t : (i : Fin n) → C.label (d i))
    (inside : ∀ i, Interior ((Ship.yardSky C b hN p).chamber 0)
      (Read.probes C N p k (Station.choose C.path.levels b k x) (q_asked (C:=C) (stretch C a t)) i))
    (returns : ∀ s : Glyph.modes (Fin n), s.val.Nonempty →
      (Ship.yardSky C b hN p).rootTest (C.beta N p) (fun U =>
        (Ship.invoiceSky (jointX (stretch C a w)) (q_asked (C:=C) (stretch C a t)) fit N p U).part s) ≤
        Ship.budget C.path.levels u k) :
    (∏ i, a i) * ‖C.numeric N p (q_asked (C:=C) t) (fun i =>
      Cells.location C.S k N p (Station.choose C.path.levels b k x i)) -
      (standard C).useAt (standard C) (Station.tested C.path.levels b k x) (jointX w)‖ ≤
      Poly.price (fun _=>1) (Read.maxProfile C (Station.tested C.path.levels b k x) (jointX (stretch C a w))) *
        Ship.budget C.path.levels u k := by
  have actual := Read.full_cost hc (Ship.fittingSky fit) (Ship.budget_pos C.path.levels u k).le
    (Ship.yardSky C b hN p) inside returns
  rw [physical, gaussian, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Finset.prod_pos (fun i _ => ha i))] at actual
  exact actual

end YM.Integration.WilsonReporterWeightedOrdinary
