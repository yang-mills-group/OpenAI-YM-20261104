import YM.FullVolume.Roll.Spindle

/-! Fund the auxiliary manuscript wage at the original physical income pocket.
The register, program and emitted shelter keep their original physical data. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

namespace ActualHighWage
def qStage (s1 s2:RG.Stage) : RG.Stage := { s2 with supportExponent:= 1000*(10+s1.supportExponent)+s2.supportExponent, price_pos:= by linarith only [s1.price_pos,s2.price_pos] }
def qp (A: ℕ→RG.Stage)(x y:ℕ) :ℝ:= (qStage (A x) (A y)|>.supportExponent)+ 4
lemma qpLarge (A: ℕ→RG.Stage) (x y:ℕ): (A y).supportExponent+3 ≤ qp A x y:= by change _≤1000*(10+(A x).supportExponent)+(A y).supportExponent+4; linarith only [(A x).price_pos] -- include issue
end ActualHighWage

section
variable {G : Gauge} {Z : ChartRatio G}
theorem actualBudget (s : Sheet G) (K : MapPrices) (hZ : LocalRatio Z)
    (r : ℕ→ℕ→ℕ) (t earn ε : Return.Wages) (Y : ℕ) (ht : ∀ j i,0≤t j i) (hEarn : ∀ j i,0≤earn j i) (he : ∀ j i,-(1/2:ℝ)<ε j i ∧ ε j i<0)
    (l : ℕ) (hl : 500≤l) :
    ∃ (f : ℕ→ℕ) (C : Programs s) (v : Return.Wages) (L : Targets s K) (E : Expenses L), s.floorL≤f ∧
      (∀ j i,(L j i).table=Z ∧ (L j i).halo=l ∧ (E j i).earn=earn j i ∧ (E j i).wanting=ε j i ∧ (E j i).degrees=Y) ∧
      ∀ g, f≤g → Base {s with floorL:=g} K Z C v t r E := by
  obtain ⟨b,hb,hx⟩ := Psalm.Refit.first s K hZ
  obtain ⟨f,C,v,hf,hE⟩ := earlier s K r (Solo.raise t) (fun i j=> add_nonneg (ht ..) zero_le_two)
  choose L E hL hQ hC hP hT using fun j i=> aim_budget hZ (Testing.query s K j i) (earn j i) _ Y l hl (hEarn j i) (he j i).1 (he j i).2
  obtain ⟨x,-,he,H⟩ := Planning.sponsors s K L E
  refine ⟨max b (max f x),C,v,L,E,hb.trans (le_sup_left),fun j i=>⟨hL j i,hT j i,hC j i,hP j i,hQ j i⟩,fun g hl => ?_⟩
  have hb : b ≤ g := (le_sup_left (b:=f ⊔ x)).trans hl
  have hf : f⊔x ≤ g := (le_sup_right (a:=b)).trans hl
  have hG : x≤g := (le_sup_right (a:=f)).trans hf
  exact ⟨hE _ ((le_sup_left (b:=x)).trans hf),hx _ hb,
    (fun j i he Y hL=> H.1 j i he Y ((hG j).trans hL)),fun j i he Y hL=> H.2 j i he Y ((hG j).trans hL)⟩

end

variable {G : Gauge} {s : Sheet G} {O K : MapPrices} {l v : ℕ→ℕ} {D : Rolls (ThroughLaunch.raise s l)}
  {X : Further.StrongStartup.Tariffs} {Θ : Extra.Multi.Scope} {r : Bid.Worth} {u g k : ℕ→ℝ}
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (ThroughLaunch.raging s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}
variable (hG : G.Simple) (h : ThroughLaunch.Perceived s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (ThroughLaunch.raging s K) (chart G) C z t m E) (c₁ c₂ c : ℝ) (h₁ : 0<c₁) (h₂ : 0<c₂) (hc : 0<c)

include hG h h₁ h₂ hc
theorem timberHigh : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.raging s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=ActualHighWage.qp s.profile i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ Pocket R' S ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.raging s K) P),
                 B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z (rays s) mile b Q p J R' S c₁ c₂ c E₀ q η ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z (rays s) mile b Q p J R' S (1/16) (1/16) c E₀ q η ∧ Planned.Port.AtTop B'.kin ∧ Stationary.Artes.Cadre P B'.kin ∧ Next.Free.Amplify B'.M ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  have ht j i:0≤ rays s j i:=by unfold rays; linarith [(s.profile i).price_pos]
  have high (j i : ℕ) : 0 ≤ ActualHighWage.qp s.profile j i := (ht j i).trans (ActualHighWage.qpLarge s.profile j i)
  obtain ⟨j,C,z,R,E,hv,hU,hL⟩:= actualBudget s (ThroughLaunch.raging s K) (chart_ok G) mile (rays s) (ActualHighWage.qp s.profile) (fun _ _=>-(7/16)) 0 ht high (fun _ _=> by norm_num) 500 le_rfl
  obtain ⟨k,hK⟩:= Height.beneath s (ThroughLaunch.raging s K) E; obtain ⟨bt⟩:= Psalm.baton_exists G
  obtain ⟨x,hx⟩:= faceting s z h₂
  obtain ⟨x',hx'⟩:=faceting s z (by norm_num: 0<(1/16:ℝ))
  refine ⟨v⊔(j⊔(k⊔(x⊔x'))),C,z,R,E,bt,le_sup_left,hU,fun l hl=> ⟨Rolls.exists_rolls _ hG,fun D=>?_⟩⟩
  obtain ⟨hy,hj⟩ := sup_le_iff.mp hl; obtain ⟨hv,hJ⟩:=sup_le_iff.mp hj; obtain ⟨hu,he⟩:=sup_le_iff.mp hJ
  obtain ⟨he,he'⟩:= sup_le_iff.mp he
  obtain ⟨Y,hY⟩:= (hL l hv).width D bt; refine ⟨Y,fun w hw=>?_⟩; obtain ⟨u,⟨K⟩,c',hY⟩:=hY w hw
  refine ⟨u,K,c',fun K'=>?_⟩; obtain ⟨F,S,hS,H⟩:= pockets K K'
  exact ⟨F,S,hS,H,fun E₀ ξ=> employeesUK hG h hy (hL l hv) c₁ c₂ c h₁ h₂ hc ht (fun i j L h h' =>hx _ _ L h ((he j).trans h')) (fun i j L h h' =>hx' _ _ L h ((he' j).trans h')) (fun j i h L h' => hK j i h L ((hu j).trans h')) (fun j i _=> ⟨(ActualHighWage.qpLarge s.profile j i).trans (hU j i).2.2.1.ge,le_rfl,by rw [(hU j i).2.1]⟩) (fun j i _=>by rw [(hU j i).2.2.2.1]; norm_num) K hY S H E₀ ξ⟩
end YM.PhysicalNext.Repeat.Roof
end
