import YM.RG01Estimate.Plan
import YM.RG01Estimate.Routed
/-!
 # Pre-Scale demands and viability for Precise. All-order Stamped via `Paid.volume` prior to
 reporter threshold (no period-dependent schedule again). Can choose folio meters huge; *model*
 budgets ownership after launch isn't proving registration feasibility.
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
open Cub Circlet Graces Roost
open Laplace Pressure ConnectedActivityE6 Evoc Push Deck ConnectedActivityE6.Coat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {M:Metals G} (D:Rolls M.p)
variable {q:Targets M.p M.K}{p:Expenses q}{w:Return.Wages}{U:ℕ→ℝ}
   (R:PhysicalNext.Repeat.Register D p w U) {c:Protection D} (T:Delays c) {F:ℕ→ℕ→Postage} (S:Time.Scouts (F:=F))

structure Request (j i r:ℕ) where
    meters : ℕ
    minStudio : ℕ
    minPrice : ℕ
    loss : ℝ
    positive : 0<loss
    -- stage function producing width-&-rate disclosures. Provers for rendered Packets (and on
    -- arbitrary customer P supply) can choose here deterministic H.costs & exponents from uptake.
    -- Gates that need those envelope functions, on ANY realization V', can be requested here too
    -- as `extras :: t, ResetDemand t`. This can't assert the actual cost with future trajectory!
    mark {h:4 ≤ j} {ℓ n:ℕ} (f:Precise.Horizon M D j i ℓ r n h) (_:ℕ)(_ _ _ _:ℝ→ℝ) (_:ℝ→Prop) : Prop
    incomes (h:4 ≤ j) (ℓ n : ℕ) (f:Precise.Horizon M D j i ℓ r n h) : minPrice ≤ n → minStudio ≤ ℓ → ∃ (e:ℕ)(s a b d':ℝ→ℝ)(Q:ℝ→Prop),
      Cookie G (D.L j) s ∧ Cookie G (D.L j) a ∧ Cookie G (D.L j) b ∧ Cookie G (D.L j) d' ∧ (∀ᶠ t in atTop,0 ≤ s t) ∧ mark f e s a b d' Q ∧ (∀ᶠ t in atTop, Q t)

-- j,i stage indexing without requiring Subsingleton proof irrelevance across stage.
structure Demand (G:Gauge) where
   wish {M:Metals G} (D:Rolls M.p) (j i r:ℕ) : Request D j i r
   retention (s:ℕ→RG.Stage) (_z:Return.Wages) -- optional preL predicate? don't use v in τ? permit.
     (j i:ℕ) : ℝ
   available (s:ℕ→RG.Stage) (z:Return.Wages) (j i:ℕ) : 0 < retention s z j i

variable {j i r ℓ : ℕ}

def tight (b m ℓ r k: ℕ) : Prop:= ∀ B:ℕ,1 ≤ B →
     house b B (m*B) (Fate.steps r)+optic b B (m*B)+5 ≤ Meadow.studio ℓ B ∧ Meadow.studio b B ≤ Meadow.studio ℓ B ∧
       4*Meadow.studio ℓ B+16 ≤ k*(1+B) ∧ 2*Trio.base ℓ B < k*(1+B)
lemma exercises (b m k' r:ℕ):∃ (ℓ :ℕ), k' ≤ ℓ ∧ tight b m ℓ r (Trio.maxFixed ℓ):= by
   obtain ⟨ℓ,hL,hP⟩:= Precise.passport_hub m r b
   refine ⟨ℓ+k', Nat.le_add_left ..,fun B hB=> ?_⟩
   obtain ⟨hp,hv⟩:= hP B hB; have hh := Trio.roof (ℓ+k') B hB
   have ht: ℓ ≤ ℓ+k' := Nat.le_add_right ..
   have hW : Meadow.studio ℓ B ≤ Meadow.studio (ℓ+k') B := by unfold Meadow.studio Meadow.roomSize Mint.width; gcongr
   have hx : 2*Trio.base (ℓ+k') B < Trio.maxFixed (ℓ+k')*(1+B):= by
      apply lt_of_le_of_lt hh; apply Nat.mul_lt_mul_of_pos_left <;> (try unfold Trio.maxFixed Trio.base) <;> omega
   exact ⟨hp.trans hW,hv.trans hW,le_of_lt (lt_trans (show 4*Meadow.studio (ℓ+k') B+16 < 2*Trio.base (ℓ+k') B from by unfold Trio.base Trio.tent; omega) hx),hx⟩

def Crate (R:PhysicalNext.Repeat.Register D p w U)(h:4 ≤ j)
    (Q:Request D j i r)
    (S:Time.Scouts (F:=F))(k:ℕ)(y:ℝ) : Prop :=
   ∃ (ℓ n : ℕ)(f:Precise.Horizon M D j i ℓ r n h)(e:ℕ)(s a b d':ℝ→ℝ)(X:Precise.Folio D h f e s a b d'),
      r+1+(M.p.profile i).order ≤ n ∧ Q.minPrice ≤ n ∧ Q.minStudio ≤ ℓ ∧
        Cookie G (D.L j) s ∧ Cookie G (D.L j) a ∧ Cookie G (D.L j) b ∧ Cookie G (D.L j) d' ∧
        tight ((q j i).halo) Q.meters ℓ r k ∧ Cookie G (D.L j) (Precise.wage D h f X) ∧ ∃ Y : ℝ→Prop, Q.mark f e s a b d' Y ∧
         ∀ t, y ≤ t → Y t ∧ 0 ≤ s t ∧ Precise.OpenAt D R h f X (S j i) t ∧ ∀ β:ℝ,betaF G t (D.L j)/2 ≤ β → β ≤2*betaF G t (D.L j)→
           gStep β^(r+1)*Precise.wage D h f X t ≤ gStep β ^ ((r:ℝ)+1-Q.loss)
lemma buys (h:4≤j) (h':(p j i).wanting ≤ -(1/4:ℝ)) (ht:StepStages j i)(Q:Request D j i r) : ∃ k₀:ℕ, ∃ y:ℝ,
   Crate D R h Q S k₀ y := by
  obtain ⟨ℓ,hm,hK⟩:= exercises (q j i).halo Q.meters Q.minStudio r; let n:= r+1+(M.p.profile i).order+Q.minPrice
  obtain ⟨H,hF⟩:= Precise.horizons R h ht (S j i) (ℓ:=ℓ) (show r+1+(M.p.profile i).order ≤ n from Nat.le_add_right ..) h'
  obtain ⟨e,s,a,b,d',P,hp,ha,hb,hd,hQ,hs,hX⟩:= Q.incomes h ℓ n H (Nat.le_add_left ..) hm
  obtain ⟨f,hY,hf⟩:= hF e s a b d' hp ha hb hd
  obtain ⟨x,hx⟩:= eventually_atTop.mp (hX.and (hQ.and (hf.and (Precise.priced Q.loss Q.positive hY r))))
  exact ⟨_,x,ℓ,n,H,e,s,a,b,d',f,Nat.le_add_right .., Nat.le_add_left ..,hm,hp,ha,hb,hd,hK,hY,P,hs,hx⟩
end YM.RG01Estimate.Chart
