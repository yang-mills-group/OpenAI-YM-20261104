import YM.OPE.Compatible.Kash.Glaze
import YM.OPE.Compatible.Kash.Logs
/-!
# Sap.EOM radical membership at launch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark Quit.Jac
variable {u d s r l k m:ℕ}{W I E:Type}{τ:Phase→ℕ}
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hr:LocalRatio P)(hp:4  ≤  s)(hs:G.Simple)(hv:0  ≤  t)(R:Patch){n:Side}(x y:Site n)(H:Even n.val)
local notation "M!"=> CountL n R.L
local notation "Y!"=> solar G d τ
local notation "μ"=> lapPrice (Patch.L R) l
section
open Quit.Jac Ibis
variable {Γ:I→ℝ}{Y:Phase}{σ:Filter I}
noncomputable def PostQ (r:ℕ)(h:Antitone τ)(p:solar G (d+r) τ):solar G d τ:=
        match r with
        | 0 =>p
        | r+1=> PostQ r h (slipK h p)
lemma Post_mem (a:Axis)(K:ℕ)(p:solar G (d+K) τ)(h:Antitone τ)(he:p∈ SailSap A hr hp hs hv R a l): PostQ K h p∈ SailSap A hr hp hs hv R a l:=by
       induction K with
       | zero=>exact he
       | succ k ih=> exact ih (slipK h p) (thaws A hr hp hs hv R _ _ _ he)
lemma valuationS (K:ℕ)(p:solar G (d+K) τ)(h:Antitone τ)(x:Site n)(v:Bid.Dir G n): mind (PostQ K h p).val n x v= Ū^K*mind p.val n x v:=by
        induction K with
        | zero=> rw [pow_zero,one_mul];rfl
        | succ k ih=> rw [PostQ,ih]; erw [show mind (slipK h p).val n x v= Ū * mind p.val n x v from congr_fun (DelayK ..) v,pow_succ,mul_assoc]
lemma activePost (p:I→solar G (d+r) τ)(h:Antitone τ)(hv:Alive σ Γ p): Alive σ Γ (fun i=>PostQ r h (p i)):=by
        induction r with
        | zero=> exact hv
        | succ r ih=> exact ih _ (SlipLive h _ hv)
end
section
open Quit.Jac Ibis Flume.Script
variable {V:I→ℝ}(A:(j:I)→Alps K S s (V j)) {I':I→Type}[∀ i,Fintype (I' i)] (p:(i:I)→I' i→RootEdge)(f:(i:I)→Libra.Keys G (I' i)→G.Color)
variable (e:RootEdge) {Γ:I→ℝ}{U:Filter I}(Hk:∀ i, BudY e false r (p i) (f i)) (h:Tendsto Γ U atTop)(hx:RateLE U Γ V 0)(hc:Arid Γ U p) (he:∀ j:G.ColorIndex,∀ i:Phase,Tonic Γ U (fun i=>(Phone G).coord j ∘ f i) (r+i.val)) {P₀:Clip}(hvv:∀ j,(A j).clip=P₀)(hV:0 ≤ V)
variable (H':Phase)(a:Axis) (hF:r+1≤d+H'.val)(hΘ:∀ i,StencilTax (d+H'.val) k ≤ τ i)(hg:l+l< k) (hτ:Antitone τ)
include h hx hvv hc he Hk hF hV hτ hΘ hg
set_option quotPrecheck false
structure Evolve (Γ:I→ℝ)(U:Filter I)(p:I→solar G d τ)(A:(j:I)→ Alps K S s (V j))(hr:LocalRatio P)(hp:4 ≤ s)(hs:G.Simple)(hV:0 ≤ V)(R:Patch)(a:Axis)(l:ℕ):Prop where
        life : Alive U Γ p
        spirit (i:I): p i∈ SailSap (A i) hr hp hs (hV i) R a l
lemma issuer :∃ P:I→solar G d τ,Evolve Γ U P A hr hp hs hV R a l∧∀ i (n:Side),Anti n e (p i)→ ∀ x:Site n,∀ Y:Bid.Dir G n,mind (P i).val _ x Y=Ū^(H'.val) * (School e false A i (p i) (f i) r _ x Y):=by
        obtain ⟨v,hB,H⟩:=Comet A p f h hc e false Hk he hx hvv hV hF hs (τ:=τ); let Y i:=PostQ H'.val hτ (v i)
        refine ⟨Y,⟨activePost v hτ hB,fun i=> Post_mem (A i) hr hp hs (hV i) R a _ _ hτ (Hero _ hr hp hs (hV i) R e (f i) _ _ hF hΘ hg (Hk i) (H i) a)⟩,fun i n hx x Y' =>?_ ⟩
        have he:∀ᶠ n:Side in atTop,∀ x:Site n,mind (v i).val _ x=Cake (sett n x e) false (Dune (A i)) (Rh (A i)) (f i∘ dip (p i) n x) r:= (H i).mono fun i hi=> congr_fun hi; exact (valuationS ..).trans (congr_arg _ (congr_fun (terroir e (A i) (p i) r false (f i) (Hk i|>.sm) (hV i) hx (v i) he x) _))
end
end YM.OPE.Variance
