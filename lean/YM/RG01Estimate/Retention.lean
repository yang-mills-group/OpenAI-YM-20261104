import YM.RG01Estimate.Demand
/-!
 # post purchase w Wage order any stance
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
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Evoc Push Deck
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {M:Metals G} (D:Rolls M.p)
variable {q:Targets M.p M.K}{p:Expenses q}{w:Return.Wages}{U:ℕ→ℝ}
   (R:PhysicalNext.Repeat.Register D p w U) {c:Protection D} (T:Delays c) {F:ℕ→ℕ→Postage} (S:Time.Scouts (F:=F))
   (X:Demand G)
lemma rprice (s:ℕ→RG.Stage) (v:Return.Wages):∃ u:ℕ→ℕ,∀ j i,StepStages j i→∀ L: Side,u j ≤ L.val →
    Height.away (s i)*(v j i/L.val) ≤ X.retention s v j i / 2:= by
   have h j i : ∀ᶠ n:ℕ in atTop, Height.away (s i)*(v j i / (n:ℝ)) ≤ X.retention s v j i/2 := by
     have he : Tendsto (fun n:ℕ=> Height.away (s i) * (v j i/(n:ℝ))) atTop (𝓝 0):= by
         simpa using! (((tendsto_const_nhds (x:=v j i)).div_atTop tendsto_natCast_atTop_atTop).const_mul (Height.away (s i)))
     exact he.eventually (ge_mem_nhds (half_pos (X.available s v j i)))
   choose u hu using fun j i=> eventually_atTop.mp (h j i)
   exact ⟨fromMax u, fun j i hi L hL=>hu j i L ((le_fromMax u hi).trans hL)⟩
lemma margin (v:Return.Wages) : ∃ T':Delays c, DelayLe T T' ∧ ∀ V,DelayLe T' V → ∀ j i,StepStages j i→∀ x, V.betaEntry j ≤ x→
        Activation.glyph G (D.L j) x ≤ X.retention M.p.profile v j i/2:=by
   have h j i (_hi:StepStages j i) :∀ᶠ t:ℝ in atTop,Activation.glyph G (D.L j) t ≤ X.retention M.p.profile v j i/2:= by
       filter_upwards [(Rate.power (G:=G) (L:=D.L j) (a:=-(1/4)) |>.below (by norm_num) (X.retention M.p.profile v j i/2) (half_pos (X.available M.p.profile v j i)))] with x hx
       exact (le_abs_self _).trans hx
   obtain ⟨s,-,hx,hY⟩:= collect_upper T.betaEntry _ fun j=> eventually_transitions j _ _ (h j)
   exact ⟨{T with betaEntry:=s},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ h j i hi x hV=>hY j x ((h.beta _).trans hV) i hi⟩

-- usable aperture at any contributed step. y ≤ betaEntry, so ANY t after j respectively.
def Shipping : Prop:= ∀ j i, StepStages j i→ ∀ h:4 ≤ j, ∀ r :ℕ,r≤j→ ∃ k y,Crate D R h (X.wish D j i r) S k y ∧ y ≤ T.betaEntry j ∧ k ≤ T.shells j ∧ 1 ≤ T.growth j
lemma sails (hp : ∀ j i,(p j i).wanting ≤ -(1/4:ℝ)):∃ W:Delays c,DelayLe T W ∧ ∀ V,DelayLe W V → Shipping D R V S X:=by
   have hh (j i r:ℕ): ∃ (k:ℕ)(y:ℝ),∀ h: 4≤j, StepStages j i → Crate D R h (X.wish D j i r) S k y := by
       by_cases h:4≤j ∧ StepStages j i
       · obtain ⟨k,x,hx⟩:= buys D R S h.1 (hp ..) h.2 (X.wish D j i r); exact ⟨k,x,fun _ _=>hx⟩
       exact ⟨0,0,fun hi hv=> (h ⟨hi,hv⟩).elim⟩
   choose k y hs using hh
   let z j i:= Finset.sup (Finset.range (j+1)) (k j i)
   have hF j i : ∀ᶠ x in atTop,∀ r∈Finset.range (j+1),y j i r≤x:= (Finset.range (j+1)).eventually_all.mpr (fun r _=> eventually_ge_atTop _)
   obtain ⟨s,-,hw,hY⟩:=collect_upper T.betaEntry _ fun j=> eventually_transitions j _ _ (fun i _=>hF j i)
   refine ⟨{T with betaEntry:=s,growth:=fun i=>T.growth i+1, shells:=fun j=>T.shells j+fromMax z j},
      ⟨hw,le_rfl,fun j=> Nat.le_add_right ..,fun i=> Nat.le_succ _⟩,fun V h j i hi hJ r hr=> ?_⟩
   have hG := (show s j ≤ V.betaEntry j from h.beta _)
   have ht := (show T.shells j+fromMax z j ≤ V.shells j from h.shells j); let q:=k j i r
   have hK:= Finset.le_sup (f:=k j i) (s:=Finset.range (j+1)) (Finset.mem_range.mpr (show r < j+1 from Nat.lt_succ_of_le hr))
   exact ⟨_,_,hs j i r hJ hi, hY j _ hG i hi r (Finset.mem_range.mpr (by omega)), hK.trans ((le_fromMax z hi).trans ((Nat.le_add_left _ _).trans ht)), (Nat.le_add_left 1 _).trans (h.growth _)⟩
end YM.RG01Estimate.Chart
