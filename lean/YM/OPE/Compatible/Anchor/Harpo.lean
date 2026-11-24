import YM.OPE.Compatible.Anchor.Rich
/-! # A genuine projected lift from offshell EOM space by compact symmetry -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
-- general E,F finite
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable (A:G.El→ E→ₗ[ℝ] E)(B:G.El→ F→ₗ[ℝ] F)
structure Orbit (A:G.El→ E→ₗ[ℝ] E):Prop where
     turn (x:E) : A 1 x=x
     turns (x y:G.El)(e:E) : A (x*y) e=A x (A y e)
     sphere : Continuous fun y:G.El× E=> A y.1 y.2
variable (h:Orbit A)(hp:Orbit B)
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
-- commute with C* in sections.Repeat
local notation "µ"=> G.probHaar
lemma coEqual {C:E→ₗ[ℝ] F}(hc:∀ s:G.El, C ∘ₗ A s=B s ∘ₗ C)(h:Orbit A)(hp:Orbit B):
    ∃ D:F→ₗ[ℝ] E,(∀ s:G.El,D ∘ₗ B s = A s∘ₗ D)∧ C∘ₗ D ∘ₗ C=C:=by
        let T:=LinearMap.range C; obtain ⟨S,hs⟩:= C.rangeRestrict.exists_rightInverse_of_surjective C.range_rangeRestrict; let P:= T.subtype.leftInverse; let R:= S ∘ₗ P; have he(p): C (R (C p))=C p:=by let v:= C.rangeRestrict p; rw [show R (C p)= S v from congr_arg S (T.subtype.leftInverse_apply_of_inj T.ker_subtype v)]; exact Subtype.ext_iff.mp (DFunLike.congr_fun hs v)
        let ℓ (f:F)(s:G.El):= A s (R (B s⁻¹ f)); have hf(f): Integrable (ℓ f) µ:= by
             have ht:Continuous (ℓ f):= h.sphere.comp (continuous_id.prodMk (R.continuous_of_finiteDimensional.comp (hp.sphere.comp (continuous_inv.prodMk continuous_const)))); exact ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
        let D:F→ₗ[ℝ] E := {
             toFun f:=∫ x,ℓ f x ∂µ
             map_add' x y:=by unfold ℓ; simp_rw [_root_.map_add]; exact integral_add (hf _) (hf _)
             map_smul' a x:=by unfold ℓ; simp_rw [_root_.map_smul]; exact integral_smul .. }
        refine ⟨D,fun s=>?_,?_⟩
        · apply LinearMap.ext; intro i; let L:= (A s).toContinuousLinearMap; change (∫ x,ℓ (B s i) x ∂µ)= L (∫ x,ℓ i x ∂µ); rw [← (measurePreserving_mul_left µ s).integral_comp (Homeomorph.mulLeft s).measurableEmbedding (ℓ (B s i)), ← L.integral_comp_comm (hf i)] -- name args
          refine integral_congr_ae (Eventually.of_forall fun x=>?_); unfold ℓ; dsimp only; rw [h.turns, ← hp.turns]; simp [mul_assoc,L]
        apply LinearMap.ext; intro y; let T:=C.toContinuousLinearMap; change T (∫ x,ℓ (C y) x ∂µ)=_; rw [← T.integral_comp_comm (hf _)]; have hQ(x:G.El): T (ℓ (C y) x)= C y:=by
             unfold ℓ; rw [show B x⁻¹ (C y) =_ from (show B x⁻¹ (C y) = C (A x⁻¹ y) from (DFunLike.congr_fun (hc x⁻¹) y).symm), show T _ = _ from (show T (A x (R (C _))) = B x (C _) from DFunLike.congr_fun (hc x) (R (C _))),he, ← (show B x⁻¹ (C y)= C _ from (DFunLike.congr_fun (hc x⁻¹) y).symm),←hp.turns]; simp [hp.turn]
        simp_rw [hQ];simp
omit [FiniteDimensional ℝ E] in lemma orbitPi {Λ:Type}[Fintype Λ](h:Orbit A): Orbit (G:=G) (E:=Λ→E) (fun s=> LinearMap.pi fun (i:Λ)=> A s ∘ₗ LinearMap.proj (φ:=fun _:Λ=> E) i) :=by
    constructor
    · exact fun i=>funext fun j=>h.turn (i j)
    · exact fun x y v=>funext fun i=>h.turns x y (v i)
    exact continuous_pi fun i=> h.sphere.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
lemma orbitA (G:Gauge): Orbit (E:=G.Color) G.adjoint:=by refine ⟨G.adjoint_one,G.adjoint_mul,adContour G⟩
lemma μIncome : ∃ P: BoxC G k→ₗ[ℝ] Taylor G (k+1),(∀ s:G.El, P ∘ₗ Ahorn s= Taylor.paint s ∘ₗ P) ∧ bets G k ∘ₗ P ∘ₗ bets G k=bets G k:= by
     refine coEqual (E:=Taylor G (k+1)) (F:=BoxC G k) Taylor.paint Ahorn (C:=bets G k) ?_ ?_ ?_; · exact fun p=> LinearMap.ext fun i=> μAxis i p
     · exact ⟨TBill, fun x y e=> TPaint e x y,sweet_t⟩
     exact orbitPi (Λ:=HornIdx k) G.adjoint (orbitA G)
end YM.OPE.Variance
