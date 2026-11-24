import YM.QuadraticLocal.Travel
import YM.QuadraticLocal.Normalization.Scripts
import YM.QuadraticLocal.Shelter.Festival
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spire
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Lotus Merge Palette Trigger
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse RemainderComparison.Mosaic RemainderComparison.Serif RemainderComparison.Typeface
open Push.Local GridRenewal.Rain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n c:Side}{P : Rep G n}{V:Type}[DecidableEq V]{R:Census V}{o:V→Site n}
    {x a r p y Δ y₀ C t₀ θ c0:ℝ}
variable {T:Type*}{I:Type}{b:BudgetPoint} (A: Lamps T I G b o R) (S:StepData c n)
-- b : BudgetPoint
set_option quotPrecheck false
variable {P' : BudgetPoint}
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable (L:Gallery T I o P R)
section shift
variable (F:T → Config G c→ Poly R)(K:T→ Config G n→ Poly R)(P':BudgetPoint)
variable {O:Activities G c}{H:Hard T P' O.forced O.K (S.ratio.parent ∘ o) R}{log:T→ Config G c→ Poly R}
variable [Fintype V]
variable (m:Config G c→ℝ) (hQ:Audit (U:=O) m H (fun t=>S.push P.beta (K t)) log)
-- to include G;
include hQ
lemma postWide (d:ℝ)(ha:0≤a)(hw:∀ i,0<w i)(hP:L.E.Paid w P.p.B a d)
    (hk:S.IsKernel P.beta G)(hi:∀ t, Integrable (K t) (prior G _))(he:∀ t U,L.density t U= cyclone (globes L t)* K t U)(hL:∀ t U,(log t U).part R.quiet=0) :
    Audit (U:=O) m H (fun t=> S.push P.beta (L.density t)) (fun t U=> globes L t+log t U):=by
    intro i U; obtain ⟨hs,hv⟩:=hQ i U
    let g : Marker.Poly R →ₗ[ℂ] Marker.Poly R := Algebra.lmul ℂ (Marker.Poly R) (cyclone (globes L i))
    let f := g.toContinuousLinearMap.restrictScalars ℝ
    have hA: S.push P.beta (L.density i) U= cyclone (globes L i)* S.push P.beta (K i) U:=by unfold StepData.push; have ht:= f.integral_comp_comm (StepData.push_slice hk U _ (hi i)); simp_rw [he]; simp_rw [f.map_smul] at ht; exact ht
    refine ⟨hs,?_⟩; dsimp only at hv ⊢; rw [hA,hv,mul_smul_comm,←mul_assoc]; congr 2; -- one goal
    rw [← passes (globes L i+log i U) (show _=0 by simp_rw [Poly.part_plus, no_spark w L ha hw d hP i, hL, add_zero]),← GridRenewal.Rain.passes _ (hL ..),GridRenewal.Rain.plus]
end shift
end YM.QuadraticLocal.Spire
