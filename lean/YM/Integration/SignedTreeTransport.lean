import YM.Integration.ActualSignedCore
import YM.Integration.WilsonWholeLimit
import YM.Integration.OPETreePhysical

/-! The complete finite-product source and the normalized mean of a
grouped signed observable on the original Wilson action and coarse law. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedTreeTransport
open Function Filter Set MeasureTheory Spec OPE OPE.Orbits PhysMS Wilson OPE.Therm
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {n m i d : ℕ}

/-- The same top-level activity, including its complete action, on the exact
chosen history is transported before integrating against its coarse law. -/
def mean (C : Family G) (N p m : ℕ) (hm : m ≤ N) (b : Config G (C.side N p) → ℂ) : ℂ :=
  ∫ U, actualSignedTransport C (N := N)
    (fun W => ((C.path.rep N p N).eval W : ℂ) * b W) hm U ∂scene C.path N p m

theorem mean_eq (hC : C.Makes) (N p m : ℕ) (hm : m ≤ N) (b : Config G (C.side N p) → ℂ)
    (hb : Continuous b) : mean C N p m hm b = moment (C.beta N p) b := by
  have hc : Continuous (fun W : Config G (C.side N p) =>
      ((C.path.rep N p N).eval W : ℂ) * b W) := by
    rw [(hC.wilson.starts N p).2]
    exact (Complex.continuous_ofReal.comp (bare_cont _)).mul hb
  rw [mean, actualSignedTransport_mean C hC (le_refl N)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hm,
    (hC.wilson.starts N p).2, moment_formula _ _ (continuous_integrable _ hb)]
  rw [Complex.real_smul, Complex.ofReal_inv]

def jointFields (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) :
    Fin (n+m) → E C.labels (max i d) :=
  Fin.append (RG11.Fields.up C.labels (le_max_left i d) ∘ v)
    (RG11.Fields.up C.labels (le_max_right i d) ∘ w)

/-- Every independent input and exterior field enters the same Wilson
configuration at its native rounded site and at its full physical scale. -/
def observable (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Points (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    Config G (C.side N p) → ℂ :=
  WilsonWholeLimit.product (r • x).ofLp
    (Frame.born (d := fun _ : Fin (n+m) => max i d) J r (jointFields v w)) N p

theorem observable_continuous (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Points (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    Continuous (observable J r x v w N p) :=
  WilsonWholeLimit.product_continuous .. 

theorem observable_limit (F : Final C f S) (hS : Services C f S) (J : ℝ → PhysMS.tower S)
    (r : ℝ) (hr : 0 < r) (x : Points (n+m)) (hx : x ∈ conf (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) :
    Tendsto (fun a : ℕ × ℕ => moment (C.beta a.1 a.2) (observable J r x v w a.1 a.2))
      f.fuse (𝓝 (OPETreePhysical.pair F J none r x v w)) :=
  WilsonWholeLimit.rounded_tendsto_separated F hS
    (Orbits.names (Frame.born (d := fun _ : Fin (n+m) => max i d) J r (jointFields v w)))
    (r • x) (Work.A05.smul_conf hr hx)

end YM.Integration.SignedTreeTransport
