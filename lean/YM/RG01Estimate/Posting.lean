import YM.RG01Estimate.Stamped
import YM.RG01Estimate.SafeVac
import YM.RG01Estimate.RoutedAdapter
/-!
 # Period and Power authorization
 This is all within `Stamped` on Factor A. Keep Heady.scene vouchers and actual
 path context; apply before reset and occupancy hooks (post not inferred).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Chart
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {M:Metals G} {D:Rolls M.p} (X:Demand G){A:Alloy M D}(R:Factor A)
    (H:Stamped X R)

local notation "T" => A.B.a
section scene
variable (m:ℕ)
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "x" => A.B.a.clock.hatBeta m
local notation "b" => A.B.a.clock.coverSize m
local notation "P" => A.B.a.clock.adm (m+1)

-- extant costs & requirements
structure Issue (X:Demand G)(m:ℕ)(r:ℕ) where
   ℓ : ℕ
   n : ℕ
   horizon : Precise.Horizon M D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) ℓ r n (A.B.a.clock.adm (m+1))
   e : ℕ
   s : ℝ→ℝ
   a : ℝ→ℝ
   c : ℝ→ℝ
   d : ℝ→ℝ
   folio : Precise.Folio D (A.B.a.clock.adm (m+1)) horizon e s a c d
   -- incomes and meters follow
   period (p:ℕ) : 4*Meadow.studio ℓ (A.B.a.clock.coverSize m)+16 ≤ (A.B.a.S.side m p).val ∧
       2*Trio.base ℓ (A.B.a.clock.coverSize m)<(A.B.a.S.side m p).val
   enough : r+1+(A.B.a.budget m).order ≤ n
   stipulated : let Q:= X.wish D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) r; Q.minPrice≤n ∧ Q.minStudio≤ℓ
   spends : let Q:= X.wish D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) r; ∃ Y,Q.mark horizon e s a c d Y ∧ Y (A.B.a.clock.hatBeta m)
   width : let k:= (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo; let s:= A.B.a.clock.coverSize m
           house k s ((X.wish D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) r).meters * s) (Fate.steps r) + optic k s ((X.wish D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) r).meters*s)+5 ≤ Meadow.studio ℓ s ∧ Meadow.studio k s ≤ Meadow.studio ℓ s
   purchased : 0 ≤ s (A.B.a.clock.hatBeta m) ∧ Precise.OpenAt D R.shape (A.B.a.clock.adm (m+1)) horizon folio (R.scout (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m)
   scaled : ∀ β∈ Shoot.band T (m+1),
      let K := (X.wish D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) r).loss
      gStep β^(r+1)*Precise.wage D (A.B.a.clock.adm (m+1)) horizon folio (A.B.a.clock.hatBeta m) ≤ gStep β^((r:ℝ)+1-K)

include H
lemma posts (r:ℕ)(hr:r≤J) : Nonempty (Issue R X m r):= by
    obtain ⟨k,y,⟨ℓ,n,F,e,s,a,c,d',Z,hF,hU,hA,hv,hh,hC,hD,hM,hK,Y,hτ,he⟩,hx,hy,hB⟩:= H.shipping _ _ (step_paid T m) (P) _ hr
    obtain ⟨hp,hw,Hκ,hW⟩:= he x (hx.trans (A.B.valid.pays m))
    obtain ⟨hσ,hB',hP,hμ⟩:= hM (b) (A.B.a.budget m|>.B_pos)
    have hg (p:ℕ): k*(1+b) ≤ (A.B.a.S.side m p).val:= by
        let Y := 1+b+A.B.a.clock.coverSize (m+1); have hk : 1 ≤ Y:= by unfold Y; omega
        exact le_trans (Nat.mul_le_mul hy ((Nat.le_add_right ..).trans (show Y ≤ Y^(A.delay.growth J) from (pow_one Y).symm.trans_le (Nat.pow_le_pow_right hk hB)))) (A.B.valid.volume m p)
    have hh:(A.B.a.params m).order=(M.p.profile (I)).order:= congr_arg RG.Stage.order (params_eq A.B.valid m)
    refine ⟨⟨_,_,F,_,_,_,_,_,Z,fun i=>⟨hP.trans (hg i),hμ.trans_le (hg i)⟩,(show r+1+(A.B.a.params m).order ≤ n from hh.symm ▸ hF),⟨hU,hA⟩,⟨Y,hτ,hp⟩,⟨hσ,hB'⟩,⟨hw,Hκ⟩,fun β hB=>?_⟩⟩
    have hs := beta_eq A.B.valid m
    have hP := hB.1; have hx:=hB.2; rw [hs] at hP hx; exact hW β hP hx
end scene
end YM.RG01Estimate.Chart
