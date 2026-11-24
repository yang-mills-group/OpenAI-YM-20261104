import YM.LocalLTE.Quay.Rungs
import YM.LocalLTE.Quay.Via
/-!
# Shared procurement on actual clock. Stages of *arbitrary length*. Keeping pose.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
variable {G:Gauge} (M l p r K c d κ₀ :ℕ)(e:ℝ)
open YM.LocalLTE.Vault Animals
attribute [local instance] Gauge.frobInner
structure Package {X:Metals G} {D:Rolls X.p} {C:Targets X.p X.K}{P:Expenses C}{h: Return.Wages}{v:ℕ→ℝ}{Y:Protection D} (R:Register D P h v)(κ:ℝ)(p r l K d c κ₀:ℕ)(e:ℝ)(A: Delays Y) : Prop where
   bought i j : StepStages i j → let L:= D.L i; let V:= X.p.profile j; let W:= X.p.profile i
     (scaler V l L * culture W c ≤1/2) ∧ ∀ x:ℝ, A.betaEntry i ≤ x→ let y:= betaF G x L; Majesty G W d c κ₀ K κ y ∧ CrestR V W l 0 r K L e (C i j) c (R.μ i j) x ∧ weightC x K+ oath p y≤ oath p x ∧ ∀ u :ℝ, y/2 ≤ u→ u ≤2*y→ oath p x ≤ powerR p u
variable (hG:G.Simple) (H: (Vault.most G d:ℝ)*c -(1/4:ℝ)*κ₀< echoBit K-1)(ht: echoBit K < -((p+2:ℕ):ℝ))
    (hS : -(((r:ℝ)+1))/2 < echoBit K)(hY:2-e < echoBit K)
variable (G)
noncomputable def meters (ht: echoBit K < -((p+2:ℕ):ℝ))(hS : -(((r:ℝ)+1))/2 < echoBit K)(hY:2-e < echoBit K) (hG:G.Simple) (H: (Vault.most G d:ℝ)*c -(1/4:ℝ)*κ₀< echoBit K-1) (S:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a0 b V:= S.invests (X:=X) R κ a0 b V ∧ Package (X:=X) R κ p r l K d c κ₀ e V
    pays:=by
        intro X K' C P hc μ k hκ
        obtain ⟨w,hV⟩:= S.pays C P hc μ k hκ
        choose W hP using fun i j:ℕ=> Spool.aheadYear G (X.profile j) l c hG (X.profile i)
        choose X0 hX using fun i j:ℕ=> Spool.optic G (X.profile j) (X.profile i) l 0 c
        let g:= fromMax (W⊔ X0)
        refine ⟨w ⊔ g, fun L hv D h h0 T R hp h' V=>?_⟩
        obtain ⟨hz,hg⟩:=sup_le_iff.mp hv
        obtain ⟨Y,he,hQ⟩:= hV L hz D R hp h' V
        have h (i j:ℕ)(hy:StepStages i j): (D.L i).val ≥ W i j ∧(D.L i).val≥X0 i j:=sup_le_iff.mp ((show W i j⊔X0 i j≤g i from le_fromMax (W⊔X0) hy).trans ((hg i).trans (D.large i).need))
        let a (i j:ℕ)(x:ℝ):Prop:= let V:=X.profile j; let W:=X.profile i; let L:=D.L i; let y:= betaF G x L; Majesty G W d c κ₀ K μ y ∧ CrestR V W l 0 r K L e (C i j) c (R.μ i j) x ∧ weightC x K+ oath p y≤ oath p x ∧ ∀ u :ℝ, y/2 ≤ u→ u ≤2*y→ oath p x ≤ powerR p u
        have he1:1≤ e:= by linarith only [hY,bitN K]
        have hp (i j:ℕ)(hy:StepStages i j):∀ᶠ x in atTop,a i j x:= ((Work.E09.betaF_growth G (D.L i)).eventually (Spool.estate_cap (G:=G) (X.profile i) d c K κ₀ hκ H)).and ((Spool.concession (X.profile j) (X.profile i) l 0 r K (D.L i) e (C i j) c (R.μ i j) hS hY (R.consumes i j hy|>.2.1) (hX i j (D.L i) (h i j hy|>.2)) he1).and (Spool.alongT (G:=G) p K (D.L i) ht (hP i j (D.L i) (h i j hy|>.1)|>.2))) -- order
        obtain ⟨x,-,hp0,hE⟩:= collect_upper Y.betaEntry _ fun i=> eventually_transitions i _ _ (hp i); let U:Delays T:={Y with betaEntry:=x}; have ht:DelayLe Y U:= ⟨hp0,le_rfl,le_rfl,le_rfl⟩
        exact ⟨U,he.trans ht,fun A hY=>⟨hQ A (ht.trans hY), ⟨fun i j hy=>⟨hP i j (D.L i) (h i j hy|>.1)|>.1,fun k hv=>hE i k ((hY.beta i).trans hv) j hy⟩⟩⟩⟩
end YM.PhysicalNext.Repeat.Legato.Spool
