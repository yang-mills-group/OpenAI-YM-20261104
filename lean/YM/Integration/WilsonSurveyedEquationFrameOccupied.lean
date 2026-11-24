import YM.Integration.WilsonSurveyedEquationFrameInlet
import YM.Integration.WilsonSurveyedEquationFrameWick
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceInventory

/-! The deposited surveyed physical arm at its own horizon, including its vacuum term,
with the literal thermal suspension of every occupied basis rank. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameOccupied
open Finset Function Lattice RG Wilson Labels Source Source.Drops Maxwell
open PhysicalNext.Repeat.Legato PowerSeries XSpace XSpace.Rose XSpace.Normalize XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar XSpace.Structure1
open WilsonSurveyedEquationFrameBasis (projection kernel)
open WilsonSurveyedEquationFrameInlet (bank)
open WilsonPositionProgramTrialPublicJointSourceInventory (lifted)
open scoped Classical BigOperators
variable {G : Gauge} {d n : ℕ} {H : Hol G} (W : Initialize G)

theorem fixes (v : shellSector G d) : projection (On.sectionMap d v) = On.sectionMap d v := by
  apply congrArg (On.sectionMap d)
  exact Subtype.ext (On.recovers v)

theorem idempotent (p : Label G d) : projection (projection p) = projection p :=
  fixes ((observable G d).rangeRestrict p)

theorem physical (p : Label G d) :
    (bank W d).joined.evaluate (((primes G).F d).coords ((bank W d).P (projection p))) =
    (bank W d).physical.evaluate (((primes G).F d).coords (projection p)) := by
  rw [(bank W d).reads]
  have null : kernel (projection p) = 0 := by
    simp only [kernel,LinearMap.sub_apply,LinearMap.id_apply,idempotent,sub_self]
  have vz : (bank W d).ward.evaluate 0 = 0 := ((bank W d).ward.eval_linear.mk' _).map_zero
  simp only [idempotent,null,map_zero,vz,add_zero]

/-- Each term retains its own actual power of the same bare coupling. -/
theorem suspended (Y : Sample n) (x : Y.F.Sites) (i : ((primes G).F d).Index) :
    PowerSeries.X ^ ((((primes G).F d).grades i).2) *
      Bare.raw (W.tree Y.F.p) (W.surveys d) x (projection (((primes G).F d).basis i)).val =
    Taylor.expandTaylor ((W.tree Y.F.p).basis G) (fun v => (bank W d).joined.places
      (((primes G).F d).coords ((bank W d).P (projection (((primes G).F d).basis i)))) x
      ((W.tree Y.F.p).links v)) := by
  let F := (primes G).F d
  have eq := Bare.raw_calculation (W.tree Y.F.p) (W.surveys d) x F (bank W d).physical
    (bank W d).survey (F.grades i).1 (F.grades i).2
    (WilsonSurveyedEquationFrameBasis.graded (F.pure i))
  have readback := physical W (F.basis i)
  apply eq.trans
  apply congrArg (Taylor.expandTaylor ((W.tree Y.F.p).basis G))
  funext v
  exact (congrFun readback _).symm

theorem one (F : Frame G (d-4)) (A : Survey G H d) (simple : G.Simple) (hd : d ≤ 7)
    (p : Label G d) : ∃ c : ℂ, ∀(P : Period) (T : P.Tree) (x : P.Sites),
    Bare.column T A x p = Bare.raw T A x p.val + c • (1 : Bare.Series T G) := by
  obtain ⟨c,hc⟩ := WilsonSurveyedEquationFrameWick.scalar F A (-1) p simple hd
  refine ⟨c,fun P T x => ?_⟩
  rw [Bare.column_formula,hc]
  change Bare.raw T A x (p.val + c • (1:Pol G)) = _
  unfold Bare.raw
  rw [map_add,map_smul,map_one]

private theorem selected (F : Frame G d) (P : Period) (T : P.Tree) (A : Survey G H d)
    (x : P.Sites) (p : Label G d) (fixed : projection p = p) :
    Bare.raw T A x p.val =
      ∑i:F.Index,F.basis.repr p i • Bare.raw T A x (projection (F.basis i)).val := by
  have dec : p = ∑i:F.Index,F.basis.repr p i • projection (F.basis i) := by
    conv_lhs => rw [←fixed,← F.basis.sum_repr p]
    rw [map_sum]
    simp only [map_smul]
  conv_lhs => rw [dec]
  change Bare.raw T A x ((localFields G d).subtype (∑i:F.Index,F.basis.repr p i • projection (F.basis i))) = _
  unfold Bare.raw
  rw [map_sum,map_sum]
  simp only [map_smul]
  rfl

/-- The coefficients and unit are elected before the period and every placement.
All later factors are actual terms of the single joined section in `suspended`. -/
theorem original (simple : G.Simple) (hd : d ≤ 7) (v : Sec G d) :
    ∃c : Fin (d+1) → ℂ, ∀{n : ℕ} (Y : Sample n) (x : Y.F.Sites),
     regal W d Y x v =
       ∑k:Fin (d+1), ((Y.F.spacing:ℂ)^k.val)⁻¹ •
        ((∑i:((primes G).F k.val).Index, ((primes G).F k.val).basis.repr
          (lifted k.val (part d k.val v)) i •
          Bare.raw (W.tree Y.F.p) (W.surveys k.val) x
            (projection (((primes G).F k.val).basis i)).val) +
          c k • (1 : Bare.Series (W.tree Y.F.p) G)) := by
  let head := fun k : Fin (d+1) => lifted k.val (part d k.val v)
  choose c pay using fun k : Fin (d+1) => one ((primes G).F _) (W.surveys k.val) simple
    (show k.val ≤ 7 by omega) (head k)
  refine ⟨c,fun {n} Y x => ?_⟩
  unfold regal
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change ((Y.F.spacing:ℂ)^k.val)⁻¹ • Bare.column (W.tree Y.F.p) (W.surveys k.val) x (head k) = _
  rw [pay k Y.F.p (W.tree Y.F.p) x,selected ((primes G).F k.val) _ _ _ _ (head k) (fixes _)]

end YM.Integration.WilsonSurveyedEquationFrameOccupied
