import YM.GapsContact.Dusk.Shift
import YM.MergeProof.Trading
/-! Supplement purchases with a fixed booking exponent (Offer cost). Variants of
Wall.lean, Instruments, Retreat, Trading. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees    PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} 

lemma peg_budget {Ñ : ChartRatio G} (h : LocalRatio Ñ) (P : Teller G) (p e : ℝ) (m : ℕ) (l : ℕ)
    (hl : 500≤l) (hp : 0 ≤ p) (he : GapsContact.Dusk.rBase<e) (he' : e<0) : ∃ (Q : Target G P)
    (v : Target.Expense Q), Q.table=Ñ ∧ v.degrees=m ∧ v.earn=p ∧ v.wanting=e ∧ Q.halo=l ∧ Q.rate=GapsContact.Dusk.rBase := by
  let a := min P.top.supportExponent (min P.top.width P.below.width)
  let r:= GapsContact.Dusk.rBase; have hr : -(1/2:ℝ)<r:=by norm_num [r,GapsContact.Dusk.rBase];
  have hR:r<e:=he
  have ha : 0 < a := lt_min P.top.price_pos (lt_min P.top.width_pos P.below.width_pos)
  let Q : Target G P := ⟨a/10,p+2,1,r,l,hl,Ñ,h,(by positivity),zero_lt_one,(by linarith),hr,hR.trans he',by
      have hx : a≤ P.top.supportExponent := min_le_left ..
      have ht : a ≤ min P.top.width P.below.width := min_le_right ..; obtain ⟨ht,hi⟩:= le_min_iff.mp ht
      constructor
      · linarith
      constructor <;> linarith⟩
  refine ⟨Q, ⟨m,p,1,1,e,hp,zero_lt_one,zero_lt_one,?_ ,hR,he'⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩
  change p+1+1 ≤ p+2; linarith

end YM.ConnectedActivityE6
end
noncomputable section
namespace YM.PhysicalNext.Repeat
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {D : Rolls s} {v w : Return.Wages} {a : ℕ→ℝ}
    {C : Programs s} {L : Targets s K} {E : Expenses L} {Z : ChartRatio G} {bt : Baton G} {p t : Return.Wages} {r : ℕ→ℕ→ℕ}
    {P : Protection D} {u : ℕ→ℕ} {B : ℕ→ℕ→Cafe}

lemma budgetsBrake (s : Sheet G) (K : MapPrices) (hZ : LocalRatio Z)
    (r : ℕ→ℕ→ℕ) (t ε : Return.Wages) (Y : ℕ) (ht : ∀ j i,0≤t j i) (he : ∀ j i,GapsContact.Dusk.rBase<ε j i ∧ ε j i<0)
    (l : ℕ) (hl : 500≤l) :
    ∃ (f : ℕ→ℕ) (C : Programs s) (v : Return.Wages) (L : Targets s K) (E : Expenses L), s.floorL≤f ∧
      (∀ j i,(L j i).table=Z ∧ (L j i).halo=l ∧ (E j i).earn=t j i ∧ (E j i).wanting=ε j i ∧ (E j i).degrees=Y∧ (L j i).rate=GapsContact.Dusk.rBase) ∧
      ∀ g, f≤g → Base {s with floorL:=g} K Z C v t r E := by
  obtain ⟨b,hb,hx⟩ := Psalm.Refit.first s K hZ
  obtain ⟨f,C,v,hf,hE⟩ := earlier s K r (Solo.raise t) (fun i j=> add_nonneg (ht ..) zero_le_two)
  choose L E hL hQ hC hP hT hE' using fun j i=> peg_budget hZ (Testing.query s K j i) _ _ Y l hl (ht j i) (he j i).1 (he j i).2
  obtain ⟨x,-,he,H⟩ := Planning.sponsors s K L E
  refine ⟨max b (max f x),C,v,L,E,hb.trans (le_sup_left),fun j i=>⟨hL j i,hT j i,hC j i,hP j i,hQ j i,hE' j i⟩,fun g hl => ?_⟩
  have hb : b ≤ g := (le_sup_left (b:=f ⊔ x)).trans hl
  have hf : f⊔x ≤ g := (le_sup_right (a:=b)).trans hl
  have hG : x≤g := (le_sup_right (a:=f)).trans hf
  exact ⟨hE _ ((le_sup_left (b:=x)).trans hf),hx _ hb,
    (fun j i he Y hL=> H.1 j i he Y ((hG j).trans hL)),fun j i he Y hL=> H.2 j i he Y ((hG j).trans hL)⟩

end YM.PhysicalNext.Repeat
end
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {s : Sheet G} {O K : MapPrices} {l v : ℕ→ℕ} {D : Rolls (ThroughLaunch.raise s l)}
  {X : Further.StrongStartup.Tariffs} {Θ : Extra.Multi.Scope} {r : Bid.Worth} {u g k : ℕ→ℝ}
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (ThroughLaunch.bearing s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}
variable (hG : G.Simple) (h : ThroughLaunch.PaidView s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (ThroughLaunch.bearing s K) (chart G) C z t m E) (c₁ c₂ c : ℝ) (h₁ : 0<c₁) (h₂ : 0<c₂) (hc : 0<c)
include hG h h₀ hb h₁ h₂ hc
omit h₀ hb
lemma boughtBrake : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.bearing s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0 ∧ (R i k).rate=GapsContact.Dusk.rBase) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.bearing s K) P),
                 B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.currency s K l) D) bt z (rays s) mile b Q p J R' S c₁ c₂ c E₀ q η ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  have ht j i:0≤ rays s j i:=by unfold rays; linarith [(s.profile i).price_pos]
  obtain ⟨j,C,z,R,E,hv,hU,hL⟩:= budgetsBrake s (ThroughLaunch.bearing s K) (chart_ok G) mile (rays s) (fun _ _=>-(7/16)) 0 ht (fun _ _=> by norm_num [GapsContact.Dusk.rBase]) 500 le_rfl
  obtain ⟨k,hK⟩:= Height.beneath s (ThroughLaunch.bearing s K) E; obtain ⟨bt⟩:= Psalm.baton_exists G
  obtain ⟨x,hx⟩:= faceting s z h₂
  refine ⟨v⊔(j⊔(k⊔x)),C,z,R,E,bt,le_sup_left,hU,fun l hl=> ⟨Rolls.exists_rolls _ hG,fun D=>?_⟩⟩
  obtain ⟨hy,hj⟩ := sup_le_iff.mp hl; obtain ⟨hv,hJ⟩:=sup_le_iff.mp hj; obtain ⟨hu,he⟩:=sup_le_iff.mp hJ
  obtain ⟨Y,hY⟩:= (hL l hv).width D bt; refine ⟨Y,fun w hw=>?_⟩; obtain ⟨u,⟨K⟩,c',hY⟩:=hY w hw
  refine ⟨u,K,c',fun K'=>?_⟩; obtain ⟨F,S,hS,H⟩:= pockets K K'
  exact ⟨F,S,hS,fun E₀ ξ=> employeesT hG h hy (hL l hv) c₁ c₂ c h₁ h₂ hc ht (fun i j L h h' =>hx _ _ L h ((he j).trans h')) (fun j i h L h' => hK j i h L ((hu j).trans h')) (fun j i _=> ⟨(hU j i).2.2.1.ge,le_rfl,by rw [(hU j i).2.1]⟩) (fun j i _=>by rw [(hU j i).2.2.2.1]; norm_num) K hY S H E₀ ξ⟩
end YM.PhysicalNext.Repeat.Roof

end
noncomputable section
namespace YM.PhysicalNext.Repeat.Roost
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple) {s:Sheet G} {O K:MapPrices} {u g k:ℕ→ℝ} {r:Bid.Worth} {T': Further.StrongStartup.Tariffs} {Θ: Extra.Multi.Scope} {v:ℕ→ℕ} (h : ThroughLaunch.PaidView s O K u g k r T' Θ v)
-- Keep inspector typed; requirements on ANY additional profile compatible with stage Slots given external order.
include hG h
theorem tariffCommerce : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.bearing s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0 ∧ (R i k).rate=GapsContact.Dusk.rBase) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : UVNext.CouplingReset.ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (Next.Foundations.localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.bearing s K) P),
                   let Y := (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.currency s K l) D)
                   B'.a = a ∧ Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η ∧ WorksIn (D:=D) (X:=ThroughLaunch.currency s K l) R' P V S ∧
                   Use.Origins B' ∧ (AsDivisors a.S → Use.Offering B' S w (radiusW B)) ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f := by
  obtain ⟨j,C,z,R,E,bt,hv,hE,ht⟩:= Roof.boughtBrake hG h _ _ _ (by norm_num : 0<(1/16:ℝ)) (by norm_num : 0<(1/16:ℝ)) (by norm_num : 0<(1/8:ℝ))
  obtain ⟨m,hM⟩:= Yearling.batten R E
  refine ⟨m⊔j,C,z,R,E,bt,hv.trans le_sup_right,hE,fun l hl=> ?_⟩
  obtain ⟨hl,hp⟩:= sup_le_iff.mp hl
  obtain ⟨hv,hy⟩:= ht l hp
  refine ⟨hv,fun D=>?_⟩; obtain ⟨k,hp⟩:= hy D; refine ⟨k,fun w hw=>?_⟩
  obtain ⟨u',R',B,hb⟩:= hp w hw
  refine ⟨u',R',B,fun K'=>?_⟩; obtain ⟨F,S,h,hp⟩:= hb K'
  refine ⟨F,S,h,fun E ξ=>?_⟩; obtain ⟨q,η,P,hp⟩:= hp E ξ
  refine ⟨q,η,P,fun θ hθ=>?_⟩; obtain ⟨θ,hq,p,hΨ,hP⟩:= hp θ hθ
  refine ⟨θ,hq,p,hΨ,fun Q U=>?_⟩
  obtain ⟨V,he,H⟩:= Roof.honey (X:=ThroughLaunch.currency s K l) (C:=R) (D:=D) R' P U S (fun i j _=> hE i j|>.2.2.2.1) (fun j i hij L hL=> hM _ _ hij L ((hl j).trans hL))
  obtain ⟨b,hp⟩:= hP Q V; refine ⟨b,fun J=>?_⟩
  obtain ⟨W,hW,hF,hf⟩:= hp J; refine ⟨W,hW,he.trans hF,fun V hU I X A ha=>?_⟩
  obtain ⟨hy,hQ,hL,hC,hg,h',hfX⟩:= hf V hU I X A ha
  have hP:= H V (hF.trans hU); exact ⟨hy,hQ,hL,hC,hg,h',hP,Use.from_menu h'.conducts.machine.ready h'.conducts.starts, (fun hx=>Rain.glazing h' hP (by simpa only [show hC.a=A from hg] using hx) (fun j i _=> (hE j i).1)),_,hfX.choose_spec⟩
end YM.PhysicalNext.Repeat.Roost
