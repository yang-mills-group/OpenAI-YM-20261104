import YM.OPE.Compatible.Eyrie.Over
import YM.OPE.Compatible.Eyrie.Dusk
import YM.OPE.Compatible.Niche.Tech
import YM.OPE.Rough.Supply
import YM.OPE.Compatible.Calendars.Repeat
/-!
# Augmented supplies on one construction

Acquire or consume extra quantitative certificates. Here hypotheses/function
inputs still specify which purchases are needed; `FinalBeam` / `Clients.Jacob`
for actually obtaining all the properties needed for the extension on the same
construction.
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
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

variable (hG:G.Simple)
open OPE OPE.Owl
set_option quotPrecheck false
include hG
-- Chronology gift chooses instance; late delays STILL may be boosted for EOM proof
-- Purchases fixed **after** Shape incomes and Yc fiscal metadata, before committing schedules.
-- Turn Curr calendar preserves acquisition.Mon.at Demand.Roll.
variable (ε:ℝ) (a:Axis)
structure LeaseB (hG:G.Simple) (a:Axis)(ε:ℝ):Prop where
     buys (s:Sheet G)(p:MapPrices)(H:Votive.Sponsor G)(K:Votive.Seasons H)(X:Stroke.PriceBook (chart_ok G) K)(Y:ℕ→ℕ)(U:Rolls (ThroughLaunch.raise s Y))(Px:Spells.Pad G)(D:Desk (ThroughLaunch.raise s Y) X a hG)
       (hF:FrameBill D U)(P:PostCost U)(T:Protection U)(Y₀:Arms (M:=ThroughLaunch.currency s p Y) U) (V:Delays T):∃ W:Delays T,DelayLe V W∧∀ Z: Delays T, DelayLe W Z→∀ (B : Bar Z) (W':Wait B)(hP:Stock.Priced Z)(D0:Directed G W' (chart G) (ThroughLaunch.bearing s p) P),∀ C:Fuel hG s p H K a X Y U Px D (Alloy.mk P T Z B W' hP D0), C.cabinet.books=Y₀→ C.Opacity ε
set_option maxHeartbeats 200000 in
lemma mandibles {b:ℝ} (h:0<b)(hℒ:LeaseB hG a ε): ∃ C:Family G,C.path.levels.clock.kernel.penalty=b∧∀ f:Extraction.Order,∃ (F: Extraction.Order)(L:Table C.book)(P:Spec.Final C (f.refine F) L),Services C (f.refine F) L ∧ OPE.Arboreal.Trace.CrownLaw P:=by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun _=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨s,T,P,A,F₀,Y,K,hX,hR,hh_stage,l,hL,hK⟩:= producerB hG hp he (fun i=> i+1) (fun i j hij=> Nat.succ_le_succ hij) (fun i=> by omega) hE
  obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
  obtain ⟨Kc,L,hki⟩:= oyster s W V hV
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hh_stage.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (ThroughLaunch.bearing s T) ho
  obtain ⟨A₁⟩:= Next.Rank.exists_budget G
  let l':ℕ→ℕ:= l⊔L⊔μ
  let τ(i:ℕ):= l' i+16; let M:=ThroughLaunch.currency s T τ
  have hl' : l ≤ l' := le_sup_left.trans le_sup_left
  have hL' : L ≤ l' := le_sup_right.trans le_sup_left
  have ht': l' ≤ τ := fun i=>Nat.le_add_right ..
  obtain ⟨⟨D⟩,H⟩:= hK τ (hl'.trans ht') a; obtain ⟨P',hZ⟩:= D.enrich; let B:=Classical.choice (Spells.curtainL G)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H D P' B hZ
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨V',h₁,bx,hK⟩:= hH Q J₀ U
  obtain ⟨V₁,ha,hφ⟩:= shower Kc V'
  obtain ⟨V₃,hV₃,hΨ⟩:= hℒ.buys s T P A F₀ τ P' B D hZ F θ bx V₁
  obtain ⟨D₀,-⟩:= Bar.exists_above V₃ 2; let I:Wait D₀:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y₁,-,H'⟩:= hK V₃ (ha.trans hV₃) D₀ I
  have hμ' (i) : μ i ≤ (P'.L i).val := ((show μ ≤ τ from le_sup_right.trans ht') i).trans (P'.large i).need
  have hG'(i):0≤ generator G i := by unfold generator; positivity
  obtain ⟨Q',Yw,hW,h₄⟩:= franchise M.K A₁ (generator G) hG' hG (hf τ).1 (hf τ).2 hμ' hμ Y₁
  obtain ⟨u,ha,hp⟩:= Wait.engine Yw hG; obtain ⟨hZb,Dρ,hK,R,hy,T0,C,Q,K,d,hF⟩:= H' Yw hW.1 hW.2.1 hW.2.2 u ha hp
  let Y':= Alloy.mk _ _ _ _ _ hZb Dρ (M:=M)
  let W':Fuel hG s T P A a F₀ τ P' B D (Y'):= ⟨_,_,R,T0,C,Q,K,d,hF,fun j=>hh_stage.prices j,fun i=>(Nat.le_add_left 16 (l' i)).trans (P'.large i).need,hR⟩
  let H':=W'.trek.hold; have hs:W'.Opacity ε:= hΨ V₃ (DelayLe.refl _) D₀ Yw hZb Dρ W' hy.1
  obtain ⟨hC,hR,hQ,hU,hW,B₀,hhB,hC₀,K₀,F₀,-,-,_⟩:= H'.placed.reception
  let Z:=W'.Holds; refine ⟨W'.Holds,(congr_arg KernelChoices.penalty (Dρ.valid.kernel.trans hX)).trans hb,fun f=>?_⟩
  obtain ⟨hFv,hcost⟩:= new_duty W'.amp W'.refQ W'.shifts H'.placed.opens (hφ V₃ hV₃) hki (hL'.trans ht')
  have hfr:Fridge Z (far Dρ.a) (fly Dρ.a):=H'.landed.1
  obtain ⟨q,b',h₁,H₂⟩:= OPE.RigE.strong_produce (C:=Z) W'.makes H'.tabs hU hfr V W hV hG hFv
  obtain ⟨g,A,L,R,z,T,E,⟨ha,he,s,hR⟩⟩:= MergeProof.Accent.rated (B:=B₀) (C:=Z) W'.makes h₁ hG hW f hU Q' hG' M.O (h₄ Z Dρ.valid B₀ hC₀)
  obtain ⟨hU,hK,A'⟩:= W'.rank_prepare; let u:=Classical.choice A'; have hy:= hK _ s.copies; obtain ⟨A',I,hI,H⟩:= Acme.emanate (W:=E) hU hG hy.1 hy.2 s he.clean.ready he.clean.tilt; let U:=(Acme.glistens hC he.clean.ready he.clean.tilt H).some
  have ht: Services Z (f.refine g) T:= ⟨hy.1,hG,⟨_,_,_,u.buy⟩,⟨A,L,R,E,he⟩⟩; exact ⟨g,T,U,ht,W'.ΦEstimate T (f.refine g) U ht (W'.fresco T (f.refine g) he ha hs (H₂ _ _ _ _ ha))⟩
end YM.PhysicalNext.Repeat.Legato
