import YM.RG06.Section.Slots
import YM.RG06.Weak.Punctured
/-!
# Direct entry expansion of a SectionData and `Family.O` itself

At the positive-link MAT letters (conjugate occurrence means conjugation
of this entry, not inverse of this number). Does not presume `Bid.pop`,
a degree cost, a specific period tail, or even soundness, to compute
the unmasked coefficient. The alternative slot expansion will prove
vanishing of negative powers in the application. These operations
include the exact engineering AND threshold scaling when reading O,
but do NOT identify terminal with a perturbative frame. All O factors
(literal a_N^(-d) and threshold powers) held fixed when differentiating.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Section
open RG06 Weak Lattice Pert Function RG Source Labels Asymptotics
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{d : ℕ}{F : Labels.Frame G d}
variable {s : Finset Cover}

def atMatrix (i j : Fin G.repDim)(sw : Bool) : G.Mat →ₗ[ℝ] ℂ :=
    let P : G.Mat→ₗ[ℝ]ℂ :=
         {toFun := fun a=> a i j
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
    if sw then ((starL ℝ).toLinearEquiv.toLinearMap.comp P) else P

@[simp] theorem atMatrix_eq (i j : Fin G.repDim)(sw : Bool)(A:G.Mat): atMatrix i j sw A= if sw then star (A i j) else A i j:=by cases sw <;> rfl

def optics (P : Links ℤ (ℕ→G.Mat)) (i : Source.Index G s) : PowerSeries ℂ := PowerSeries.mk (atMatrix i.2.1 i.2.2.1 i.2.2.2 ∘ P i.1.val)

theorem genuine {f : ℝ→Wilson.CoverConfig G}{P : Links ℤ (ℕ→G.Mat)}(h : tiled f P) (i : Source.Index G s): WritesPS (fun t=>entry (f t) i) (optics P i):= by
  unfold entry; simp_rw [← atMatrix_eq]; exact ((h _).linear (atMatrix ..)).ps

def direct (D : SectionData F) (P : Links ℤ (ℕ→G.Mat)) (v : F.Coeff) := MvPolynomial.eval₂Hom PowerSeries.C (optics P) (D.evalC v)

theorem direct_eq (D : SectionData F){f : ℝ→ Wilson.CoverConfig G}{P : Links ℤ (ℕ→G.Mat)}(h : tiled f P)(v:F.Coeff): WritesPS (fun t=>D.evaluate v (f t)) (direct D P v):=WritesPS.eval (genuine h) _

def placeColor {n:Side}(a:Links (Per n) G.Color)(o:Site n):Links ℤ G.Color:= expandAt o a

theorem direct_level (D : SectionData F){n : Side}(a:Links (Per n) G.Color)(o:Site n)(v : F.Coeff):WritesPS (fun t=>D.places v o (ray a t)) (direct D (tile (placeColor a o)) v):= direct_eq D (ray_tiled (placeColor a o)) v

def orbit {N n:ℕ}(C:Family G)(a:Links (Per (C.side N n)) G.Color) (o:Site (C.side N n))(v:C.label d) : PowerSeries ℂ:=
    PowerSeries.C ((C.S.a N:ℂ)^d)⁻¹ * direct (C.localSection d) (tile (placeColor a o)) (((C.labels.level d).scaled (C.path.levels.clock.threshold N)⁻¹) ((C.factory d N n).terminal.symm v))

/-- Exact represented physical cylinder (not density, all entries unmasked),
including the actual readout calibration (takes its inverse before differentiation).
Universal in C; valid at all N,n including if stencil wraps; the interesting
physical correlation use is only fitted levels. -/
theorem orbit_receipt {N n:ℕ}(C:Family G)(a:Links (Per (C.side N n)) G.Color)(o:Site (C.side N n))(v:C.label d): WritesPS (fun t=> C.O N n v o (ray a t)) (orbit C a o v) := by
  exact WritesPS.times (WritesPS.constant _) (direct_level (C.localSection d) a o _)

theorem orbit_unit {N n:ℕ}(C:Family G)(h:C.Makes)(a:Links (Per (C.side N n)) G.Color)(o:Site (C.side N n))(d:ℕ)(hp:C.ref d≤N): orbit C a o (C.refUnit d)=1 := by
  have he:= orbit_receipt C a o (C.refUnit d)
  rw [show (fun t=> C.O N n (C.refUnit d) o (ray a t))=(fun _:ℝ=>1) from funext fun _=> congr_fun (C.constant h d hp o) _] at he
  ext k
  rw [← Writes.coeff he k,show (1:PowerSeries ℂ)=PowerSeries.C 1 from (map_one _).symm]; simp [iteratedDeriv_const]; by_cases h:k=0 <;> simp [h]

/-- All-q asymptotic of the *bare cylinder* at fixed actual parameters.
No cost over C, calibration or backgrounds is paid here. -/
theorem actual_jet {N n:ℕ}(C:Family G)(a:Links (Per (C.side N n)) G.Color)(o:Site (C.side N n))(v:C.label d)(q:ℕ):
    ((fun t=> C.O N n v o (ray a t)) - report (fun k=>PowerSeries.coeff k (orbit C a o v)) q)=O[𝓝 0] fun t=>t^(q+1):= Writes.bound (orbit_receipt C a o v) q
end YM.RG06.Section
