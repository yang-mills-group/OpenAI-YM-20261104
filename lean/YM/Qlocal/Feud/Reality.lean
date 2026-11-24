import YM.Qlocal.Quipu.Thunder
import YM.Qlocal.Feud.Rever
/-!
 # Certificate ported to ALL Whence.Period from State.Card.
 Use orientation always through Kernel heights and exact tag.Six.No occupancy coupons removed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Kinetic
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
namespace Peak
open Quipu Quipu.Tilt Quipu.Sonnet Tern Quipu.Eluder Incline Incline.Bookworm
open Extra.Iteration
variable (P:Patch) (K:KernelChoices){G:Gauge}{n m:Side}{a b C Λ σ:ℝ}{k N l i e':ℕ}
-- one Encoding independent of periods.Proclaim.A4 later.
variable (O: ChartRatio G) {ι:Type} [Nonempty ι] (p:Clip)(x:ι→PathData G) (L: ι→ℝ)
    (V:ι→ Layout G) (T:Finset Age)(Γ:ι→ℝ)
    (α:Type)[Fintype α] [DecidableEq α] {B0:Marker.Census α} (g:α→ℕ) {s s':ℕ} (U:ι→Stanza B0 G g s) (Y' : ∀ i,(Stanza.son (U i) s').Decision) (ψ:ι→α→Site P.L) (e t:ℕ)(w:ℝ)
variable (S:ι→Stanza B0 G g e) (u:ι→ℝ) (D:ℕ→ Senses B0→ι→Side→ℝ)
variable (h:Tilt.Certificate (b:=b) (l:=l) (N:=N) P K p O x V T Γ α g U Y' ψ e t w S u D)
local notation "th"=>chant b N (3*N)/4
variable {b₀:Clip}{H:StepData n m}{R:PathData G} (i:ι) (K':Comparison.RG02.Bulk.Kernel H b₀ R O) (o': α→Site n)(F': α→Site m)
variable (hq:H.patch=P)(hz:H.kernel=K)(hb:b₀=p)(he:R=x i)
-- phase assign compiled via ratio units, cast explicit.W.We.Me.Kernel.b. NB Site equality surgery uses patch hM. use patch.transport. 
variable (hp:Bid.Larger (G:=G) H)
variable (hφ:∀ a:α,(H.ratio).parent (F' a)=o' a ∧ HEq ((H.ratio).residue (F' a)) (ψ i a))
-- canonical vision.
local notation "Z"=> Stanza.son (S i) t
local notation "F₀"=> Comparison.RG02.Symmetry.Orbit.words
include h hq hz hb he hp hφ
lemma reality (H':Forest H.ratio)(t':H.Choices)(s₀:Senses B0)(r:ℕ) (he':k≤e)(hr:k≤r): let f:= ((Comparison.RG02.Symmetry.Orbit.words K' H' t' ((Stanza.son (U i) s').mood (Y' i) F' (V i) T) r s₀.val k) ∘ ports G n); ∀ u':rule (Coarse G) n,(Complex.ofReal (f u').re)=f u' := by
 subst b₀ R; have ht:m=below P n:=Subtype.ext (by change m.val=(below P n).val; rw [H.sizes,hq]; rfl); subst m; have hZ:H=dock P K n:= by cases H with | mk x y=> dsimp only at hq hz; subst P K; rfl
 subst H; rw [show F'= assign (dock P K n) (ψ i) o' from ?_]
 · exact (h.agreement i n hp o' K' H' t' s₀ k r hr he').2
 ext1 a; let r':=(dock P K n).ratio; change F' a=r'.assemble _; have hH:(r'.parent (F' a),r'.residue (F' a))=(o' a, (ψ i a:Site P.L)):= Prod.ext (hφ a|>.1) (eq_of_heq (hφ a|>.2)); exact Eq.trans (Ratio.unpack_at r' _).symm (congr_arg (r'.assemble) hH)
end Peak
end YM.Qlocal.Feud
