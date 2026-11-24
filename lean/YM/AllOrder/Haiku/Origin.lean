import YM.AllOrder.Ink.Pump
import YM.Next.STATIONARY.Lift.Ward
set_option autoImplicit false
noncomputable section
/-!
# Fiscal transformation rules in X projection and Ward

Coarse metric. All finite sides, fixed equation many legs. Use both exact cutoff-density
proof for Ξ and independence of lifted kernels for comparison. Keep Color section at 0.
Includes convenient life after partial cooling/cancellation through any lower assignments.
Life at m with period.V only used in this proof; schedule production later.
-/
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

section actors
abbrev life (P:ℝ→Stationary.Link G c) := input G c ∘ echo P
variable (F:ℕ→ Bills (Coarse G))
structure Etiquette (n:Side)(k:ℕ) : Prop where
 stain (v w:ℝ→Stationary.Link G n) (u:ℝ→(Site n→G.El))(x:G.El): ContDiffAt ℝ ω v 0→ContDiffAt ℝ ω w 0 → Tendsto u (𝓝 0) (𝓝 (fun _=>x)) → life (G:=G) w=ᶠ[𝓝 0] (fun t=> gauge (u t) (life v t)) → weigh v (fun i=> F i n) k= weigh w (fun i=> F i n) k
 sign (v:ℝ→ Stationary.Link G n)(s:Signed): ContDiffAt ℝ ω v 0→ weigh v (fun i=> F i n) k= weigh ((orderTurn (G:=G) s) ∘ v) (fun i=> F i n) k
-- Pump transform. commute gauge & corners
open Further.PhysicalPeriodLimitF933 Macrame
lemma billing (T:Window n m k)(x:Stationary.Link G n): input G m (convey T x)= T.links (input G n x) := by
  funext ⟨v,i⟩; rw [encode_link, Window.links,encode_link]; rfl
lemma signing (t:ℕ)(s:Signed)(x:Stationary.Link G n): convey (Ink.Echo.arm n t) (orderTurn s x)= orderTurn (G:=G) s (convey (Ink.Echo.arm n t) x) := by
  let W:= Ink.Echo.arm n t; let B:=W.cut; have hp : B = splitter (show n.val ∣ (Ink.Echo.amplify n t).val from ⟨t+1,rfl⟩):= rfl; have he(j: Site (Ink.Echo.amplify n t)) : B (s.act j)=s.act (B j):= by
    obtain ⟨j,rfl⟩: ∃ v:Cover,j=wrap _ v:= ⟨_, (wrap_lift ..).symm⟩ -- choose j=e? rw subst
    rw [hp,wrap_signed,branch,branch, wrap_signed]
  ext1 j; obtain ⟨x',a,i⟩:=j; obtain ⟨a,rfl⟩:= axisEquiv.surjective a
  change flipCoords s ℝ x (W.cut x',coord a,i)= flipCoords s ℝ (convey W x) (x',coord a,i);
  rw [flip_price, flip_price]; change (if _ then _ else _) = _; split; rename_i h;
  · change _ = - x (B (_-_),coord _,_); unfold B at *; rw [W.step_down,he]
  change _ = x (B (s.act x'),_,_); rw [he]
lemma colored (T:Window n m k) (H:Site n→G.El)(x:Config G n) : T.links (gauge H x) = gauge (H ∘ T.cut) (T.links x):= by funext ⟨j,i⟩; simp only [Lattice.gauge,Function.comp_apply,Window.links]; rw [T.step_up]
end actors
end YM.AllOrder.Haiku
