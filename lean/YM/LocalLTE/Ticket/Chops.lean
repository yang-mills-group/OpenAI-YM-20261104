import YM.LocalLTE.Ballot.Elegy
import YM.LocalLTE.Ticket.Marsh
/-!
## Buying analytic currency for canonical windows.

Choices for ranks per previous output and order authorized. Use Φ in canon at each step.
Books current report to precision goal p separate from β-price analytic ζ from Πmint.
No extrapolation through infinite-depth.N finite.Goal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
variable {G:Gauge}{p q r l:ℕ}{e:ℝ}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
-- Starting depth coefficient rate ; looser after each advance
noncomputable def grantZ (p T j :ℕ):ℝ := (↑j:ℝ)-(T:ℝ)-(p:ℝ)-2
lemma slant (p T j:ℕ)(hp:j≤T+1): grantZ p T j < - ((↑p:ℝ)+1)/2:=by unfold grantZ; have hx:= Nat.cast_le (α:=ℝ)|>.2 hp; push_cast at hx; linarith only [hx, Nat.cast_nonneg (α:=ℝ) p]
open Legato.Spool
abbrev GuideF:=ℕ→ℕ→ℕ→ℕ
-- rank tables for operator calls. depth m=amount pushed. h-stage width bound includes previous photography rank in all possible formers.
structure Gazette (ζ μ: GuideF):Prop where
   wide j i m : StepStages j i → i ≤ ζ j i m
   root j i : ζ j i 0=j -- mismatch wide if j<i: use only StepStages
   tall j i m u : StepStages u j → μ u j m ≤ ζ j i (m+1)
-- ι redundant(remove linter)
structure Series {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{M:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}(R:Register D M w v)(m:ℕ)(κ:ℝ)(q l r p N:ℕ)(e:ℝ) (V:Delays T) :Prop where
   columns : 32*(1+l) ≤ V.shells 0 -- remove replace all
   plume n : 32*(1+l) ≤ V.shells n
   grew n :1 ≤ V.growth n
   periods : ∃ u a f:GuideF, Gazette a f ∧ ∀ (i j:ℕ),StepStages i j→ ∀ n:ℕ,n ≤ N→∀ x:ℝ,V.betaEntry i≤x → LocalLTE.Fan.ManifestC (C i j) (D.L i) (R.o i j) (M i j) Push.SectorMeasure.Chi.canonical (X.p.profile j).order (X.p.profile j).power m q l (a i j n) (u i j n) (f i j n) κ e Mallow.aust x (R.μ i j)
   limits i j:StepStages i j→∀ x:ℝ,V.betaEntry i≤x → l*radiusB (betaF G x (D.L i))≤ (D.L i).val*radiusB x ∧ ∀ d≤j, Load (X.p.profile i) (X.p.profile j) l r d (D.L i) e (C i j) (R.μ i j) x∧ minSide G d≤radiusB (betaF G x (D.L i))∧ (∀ c:Side,(localSection G d).footprint (0:Site c) ⊆Animals.neighbors (l*radiusB x) 0∧(localSection G d).footprint (0:Site c)⊆ Animals.neighbors ((D.L i).val*radiusB x) 0) ∧ (∀ n:ℕ,n≤N → Spool.Resale (X.p.profile j) (X.p.profile i) l d r (D.L i) e (C i j) (R.μ i j) (grantZ p N n) (grantZ p N (n+1)) x ∧ ∀ β :ℝ,betaF G x (D.L i)/2 ≤ β → β ≤2* betaF G x (D.L i)→ x^(grantZ p N (n+1)) ≤ Spool.powerR p β) ∧ BloomP G d (X.p.profile j).supportExponent (grantZ p N 0) x
namespace Gazette
variable (f:GuideF)
-- n=0 requires wide only with he
noncomputable def acc (F:GuideF):GuideF:= fun i _ d=>
    match d with
    | 0=> i
    | n+1=> i+max (F i i n) (F (i+1) i n)
-- resolve f via recursion, not mutual
noncomputable def addenda (F:GuideF) (d:ℕ):ℕ→ℕ→ℕ:=
    match d with
    | 0=>fun i j=> F i j i
    | n+1=> let s:= addenda F n; fun i j=> F i j (i+max (s i i) (s (i+1) i))
lemma gates (F:GuideF) : let g := fun i j n=> addenda F n i j; Gazette (acc g) g ∧ (∀ i j n:ℕ, g i j n = F i j (acc g i j n)):=by
    intro g; refine ⟨⟨?_,fun i j => rfl,?_⟩,?_⟩
    · intro j i m ht; unfold acc; split; exact ht.1
      exact ht.1.trans (Nat.le_add_right ..)
    · intro j i m u hu; unfold acc; have h : u=j ∨ u=j+1:=by unfold StepStages at hu; omega
      rcases h with h|h; rw [h]; exact le_trans (le_max_left _ _) (Nat.le_add_left ..)
      rw [h]; exact le_trans (le_max_right _ _) (Nat.le_add_left ..)
    intro i j n; unfold g acc; cases n with
    | zero => simp only [addenda]
    | succ n=> rw [addenda]
end Gazette
end YM.PhysicalNext.Repeat.Legato.Spiral
