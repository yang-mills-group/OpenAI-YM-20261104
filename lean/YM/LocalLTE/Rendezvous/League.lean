import YM.LocalLTE.Estate.Call
import YM.LocalLTE.Rendezvous.Recruits
/-! Genuine selected Bolts, capacities all m. No marked estimates yet. Does not choose this Bolt using another production! Exposes more options via liftsB. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
variable {G:Gauge} (hG:G.Simple)
include hG
-- headline on selected genuine theory all admitted scales actual. Derivative.Power. shared resolution and calendars, no matched infinite/history matching; CHIPs not assumed equal across p. K residual denominator charge. Span.χ labels fixed throughout.
theorem universeQ (p n:ℕ)(Θ:ℕ→ℕ→ℕ) (K:ℝ) (κ:ℝ) (hκ:0<κ): ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A)(p0 μ:ℕ)(F:Mallow.Funding R p0 1)(M:Mallow.Preview F)(W:Mallow.Trail F μ)(P:Bolt A), A.B.a.clock.kernel.penalty=κ∧ K≤A.B.a.clock.bar ∧ ∃ (_:Mallow.Adorn F W) (_:Mallow.Cready F W),MintZ A.delay (↑(p+1):ℝ) p ∧ Mallow.Made F W M P ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧∃ Z:Mallow.ConcertZ R.target μ (p+1:ℕ),Z.strength=(fun _ _ => ↑(p+1:ℕ))∧ Mallow.ConcertZ.CalendarQ R.shape Θ Z F.κ A.delay ∧∀ N m j:ℕ,∀ hm:m<N,n ≤ (A.B.a.budget m).order ∧ ∃ s a Q,∃ H:Career F N m j s a Q,∃ k' x k,Peg F H W M k' p hm (P.history N j (m+1)) (P.history N j m) x k :=by
  let v: ThroughLaunch.Orders:= ⟨4,fun i=>6+n+i,fun i=>2+n+i,fun i=>100+(n:ℝ)+(i:ℝ)⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:=by change (100:ℝ)≤100+n+i; have hh:0≤ (n:ℝ):=(by positivity); have he:0≤(i:ℝ):=(by positivity); linarith
  have hv: ThroughLaunch.Draft v:= ⟨le_rfl,fun i j h=>Nat.add_le_add_left h _,fun i j h=>Nat.add_le_add_left h _, (by intro i j hi; change (100:ℝ)+n+i≤ 100+n+j; gcongr),fun i=> (show (0:ℝ)<100 by norm_num).trans_le (hE _),fun i=>by change _≤6+n+i; omega,fun i=>by change _≤2+n+i; omega⟩
  let b:=200*(p+1); have hh: LocalLTE.Fan.Pastel.chip (b+1)+1 < -(↑(p+1):ℝ)/2:= by unfold b LocalLTE.Fan.Pastel.chip; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) p]
  obtain ⟨X,D,A,R,hΓ,hK,hV,hO,ht,p0,F,M,W,hM,U,P,hX,hA,hζ⟩:= Legato.rising hG b p hh hκ v hv K Θ (↑(p+1):ℝ) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p]) (by unfold b; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p])
  obtain ⟨Z,hα,hω⟩:=hζ
  refine ⟨X,D,A,R,p0,b,F,M,W,P,hΓ,hK,U,hM,ht,hX,hA,Z,hα,hω,fun N m j hm=>⟨?_,?_⟩⟩
  · change n≤ (A.B.a.params m).order; rw [params_eq A.B.valid m,hV.jets]; change n≤6+n+A.B.a.clock.J m; omega
  obtain ⟨s,a,Q,H,k,k',x,hx,h,hQ,hF⟩:= hX.held N m j hm
  exact ⟨s,a,Q,H,k',x,k,hQ.symm ▸ hF.symm ▸ Mallow.pegged F H W M k' p hO hm U h x hx hG⟩
end YM.PhysicalNext.Repeat.Legato
