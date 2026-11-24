import YM.UVExt.Reach
import YM.UVExt.StrongRelay
import YM.MergeProof.Noel
import YM.MergeProof.Emanate

/-!
# Strong mixed-source bin and `Base`/`Seed` on a *common* production

Extra floor, then after-block delays, then window requirements BEFORE extracting the B and
its histories. No additional choice of cutoff law after that; the physical tables and primary
cylinders are exactly those of the Family in the same grant, although we run the bin
selection on that Family with strong witnesses. This doesn't show full-cutoff convergence!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
variable {G:Gauge}{M:Metals G}{P:Rolls M.p}{A:Alloy M P} (Y:Bolt A)(t:ℕ→ℕ)
    (Xf:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)
    (hx:∀ d,d+3 ≤ A.B.a.clock.J (t d)){cost:ℕ→ℕ→ℝ}{d':ℕ→ℕ}{T:∀ d:ℕ,SectionData ((Labels.frames G).level d)}
    (hc:dusk A.delay cost)(hN:paper M.p cost T d') (hF: d' ≤ M.p.floorL)
set_option quotPrecheck false
local notation "F'" => Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Xf
include t Xf hx hc hN hF
lemma duty :
    (∀ d:ℕ, ∃ a:ℕ→ℝ,Braze (C:=F') (T d) a) ∧ ∀ i,Push.RelayDifference.jump (A.B.a.budget i)≤ A.B.a.clock.hatBeta i:= by
    let S:= A.B.a; let J:=S.clock.J
    have hW(i:ℕ)(d:ℕ)(he:t d ≤ i):d+3  ≤  J i:= (hx d).trans (A.B.a.fits.mono he)
    have hu (i:ℕ)(d:ℕ)(he:d  ≤  J (i+1)):= hN d (J (i+1)) he _ ((hF _).trans (P.large (J (i+1))).need)
    have hw(i):= hc _ _ (step_paid _ i) _ (A.B.valid.pays i)
    constructor
    · intro d; let b:= fun i=> cost d (J i)
      have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1∧ d ≤ J (j+1) := by
         filter_upwards [eventually_gt_atTop (t d)] with i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); exact ⟨j,rfl,(Nat.le_add_right d 3).trans (hW (j+1) d hi.le)⟩
      refine ⟨b,⟨?_, ?_,?_⟩⟩
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; change Bid.Credit _ (A.B.a.params (j+1)|>.order) (A.B.a.params (j+1)|>.power) _; rw [params_eq A.B.valid]; exact (hu j d h).2.1
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; exact ⟨(hu j d h).2.2.1,(hw (j+1)).2 d h|>.1⟩
      filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi
      change 2*(1+(A.B.a|>.params _|>.columns))*sphere (A.B.a|>.params _) ((T _).stencil∪(localSection G _).stencil).card (b _) ≤ Bid.puffs (A.B.a.S.block _)*sliver (Labels.frames G|>.level d)
      rw [params_eq A.B.valid,show j+1-1=j from rfl,Extra.Iteration.block_eq A.B.valid]; exact (hu j d h).1
    intro i; change step_cost (A.B.a.params i) ≤ A.B.a.clock.hatBeta i; rw [params_eq A.B.valid]; exact (hw i).1
end YM.PhysicalNext.Repeat.Legato
namespace YM.PhysicalNext.Repeat.Legato
open UVExt.Slots
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
/-- Production with one extra exact-erasure receipt for every required target weight.
Kept the choices free in `himalayas` until after purchasing the needed prices. -/
theorem family_bind_real (hG:G.Simple) {b:ℝ} (h:0<b) : ∃ C:Family G, UVExt.inverseAt C ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧
    (∀ d,StrongBin C R (f.refine g) d) ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayas hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
  obtain ⟨Kc,L,hki⟩:= oyster s W V hV
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [H.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (ThroughLaunch.bearing s T) ho
  obtain ⟨A⟩:= Next.Rank.exists_budget G
  let l':ℕ→ℕ:= l⊔L⊔μ
  let M:=ThroughLaunch.currency s T l'
  have hl' : l ≤ l' := le_sup_left.trans le_sup_left
  have hL' : L ≤ l' := le_sup_right.trans le_sup_left
  obtain ⟨⟨P⟩,H⟩:= hK l' hl'
  have hl₁ (i) : L i ≤ (P.L i).val := (hL' i).trans (P.large i).need
  have hμ' (i) : μ i ≤ (P.L i).val := ((show μ ≤ l' from le_sup_right) i).trans (P.large i).need
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V',h₁,hK⟩:= hH Q J₀ U
  obtain ⟨V₁,ha,hφ⟩:= shower Kc V'
  obtain ⟨D,-⟩:= Bar.exists_above V₁ 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y₁,-,H'⟩:= hK V₁ ha D I
  have hG'(i):0≤ generator G i := by unfold generator; positivity
  obtain ⟨Q',Y,hZ,h₄⟩:= franchise M.K A (generator G) hG' hG (hf l').1 (hf l').2 hμ' hμ Y₁
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,hR,c,T,t,S,D',hT,hq,hu⟩:= H' Y hZ.1 hZ.2.1 hZ.2.2 a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,hhB,hC₀,K₀,F₀,-,-,_⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩
  obtain ⟨hFv,hcost⟩:= duty T t S hT.opens (hφ V₁ (.refl _)) hki hL'
  have hfr : Fridge Z (far B.a) (fly B.a) := MergeProof.freezes hG (fun N p=>⟨Guard.Keeper.sufficient (hT.nest.born N p)⟩) (duty T t S hT.opens (hφ V₁ (.refl _)) hki hL').2
  obtain ⟨P',b',h₁,h₂⟩:= strong_produce (C:=Z) hF hq hU hfr V W hV hG hFv
  exact ⟨_,UVExt.reach_any Z hG T rfl,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2 f⟩,fun f=>by
    obtain ⟨g,A,L,R,z,T,E,⟨ha,he,s,hR⟩⟩:= rated (B:=B₀) hF h₁ hG hW f hU Q' hG' M.O (h₄ Z B.valid B₀ hC₀)
    exact ⟨g,A,L,R,T,E,he,h₂ _ _ _ _ ha,s,hR⟩⟩
theorem family_bind (hG:G.Simple) {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧
    (∀ d,StrongBin C R (f.refine g) d) ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨C,-,h⟩:=family_bind_real hG h
  exact ⟨C,h⟩
end YM.PhysicalNext.Repeat.Legato
