import YM.OPE.Compatible.Anchor.Harpo
/-! # Reconstruction of ghost generators by Ward.Approved. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
noncomputable def wheelC (G:Gauge)(k:ℕ): BoxC G k→ₗ[ℝ] Taylor G (k+1):= μIncome.choose
noncomputable def armK (G:Gauge):(k:ℕ)→ Taylor G k→ₗ[ℝ] Taylor G k
     | 0=>0
     | k+1=> wheelC G k ∘ₗ bets G k
lemma amuse (v:Taylor G k)(t:G.El): armK G k (Taylor.paint t v)=Taylor.paint t (armK G k v):=by
      cases k with
      | zero=> unfold armK; simp
      | succ k=> unfold armK; rw [LinearMap.comp_apply,μAxis]; exact DFunLike.congr_fun ((μIncome (G:=G) (k:=k)).choose_spec.1 t) _
lemma Cog (v:Taylor G k): v - armK G k v∈ LinearMap.range gaugeJet :=by
      cases k with
      | zero=> rw [orchardRank]; exact Set.mem_univ _
      | succ k=> rw [← betaRank]; change bets G k _=0; rw [map_sub]; apply sub_eq_zero.mpr; exact DFunLike.congr_fun ((μIncome (G:=G) (k:=k)).choose_spec.2.symm) v
lemma cashDot (p q:G.Color): Dotty p q=inner ℝ p q:=by rw [PiLp.inner_apply]; exact sum_congr rfl fun i _=>by rw [RCLike.inner_apply]; exact mul_comm ..
lemma hubAD (p q:G.Color)(s:G.El):Dotty (G.adjoint s p) (G.adjoint s q)=Dotty p q:=by
      let F:G.Color→ₗᵢ[ℝ] G.Color:= { G.adjoint s with norm_map':=G.norm_adjoint s }; rw [cashDot,cashDot]; exact F.inner_map_map .. -- arguments
lemma sepDot {x y:G.Color}(h:∀ v:G.Color, Dotty v x = Dotty v y): x=y:=by
      ext i; have hp(v:G.Color): Dotty (Phone G i) v=v i:=by
           rw [cashDot]; change inner ℝ ((Awake (G:=G)).toBasis i) v=v i; rw [OrthonormalBasis.coe_toBasis]; rw[← OrthonormalBasis.repr_apply_apply]; rfl -- rewrite
      rw [← hp,← hp,h]
-- first ∀ χ and θ f.
end YM.OPE.Variance
