import YM.RGComparison01.Composed
import YM.RGComparison01.Drift
import YM.RGComparison01.High
import YM.RGComparison01.Agenda

/-!
 # Additional clocks for the stronger exceptional and principal estimates

 Exists with the common physical buys. Just polynomial packages
 in this file plus logs & arity. Post-delay prices can also ensure SOME
 enrollment past every perturbative n. -/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quests
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm.Solo Clockwork
open RGComparison01 Tithe Height Agenda Roof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {C : Programs s} {Q : Targets s K} {E : Expenses Q}
    {M : ℕ→ℕ→JointLoad.Heir.Record} {f z e b : Return.Wages} {r : ℕ→ℕ→ℕ}
    {hL : ℕ→ℝ}
    {c c' : ℝ} (R : Register D E f hL)
    {N m n : ℕ}

section hire
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}

def Quota (p : Q.Expense) (L:Side) (W μ c : ℝ) (o : ConnectedActivityE6.Target.Order G W) (x : ℝ) (j n ℓ : ℕ) (χ:Chi) :=
    grow G L x ^ ℓ ≤ Real.exp (Q.ε*radiusB x) ∧
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T → Stamp T→
    ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R) (Z : ℕ→ℝ), RGComparison01.Tithe.Ticket R.activities R.p Z (2*incomingE G L x) →
      ∃ (C' d v t A b r B q i : ℝ) (k : ℕ),
        (∃ N: Captain H j C' d v t A b r B q k χ, Worthy N.conduit Z (grow G L x ^ ℓ)) ∧
        Armada Q L μ p.earn x i B j k ∧
        collars G i x j n * (salary Q L μ B x j k*(1-1/2)⁻¹) ≤ betaF G x L ^ p.wanting

lemma radius_pay (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (j : ℕ) : ∀ᶠ x in atTop, grow G L x ^ j ≤ Real.exp (Q.ε*radiusB x) := by
  have h:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow j|>.mul (Rate.cutoff Q.usable (a:=-1-3/8*j))
  filter_upwards [h.below (by linarith) 1 zero_lt_one] with x hx
  apply le_trans (b:=Real.exp (Q.ε*Pressure.Stores.till x))
  · apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*Pressure.Stores.till x))
    rw [← Real.exp_add, neg_mul,add_neg_cancel,Real.exp_zero]; exact (le_abs_self _).trans (by simpa only [neg_mul,grow] using hx)
  exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_le_self ..) Q.usable.le)

lemma quotas (Q : YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W), 0<W → 0<μ →
    ∀ j n l χ, ∀ᶠ x:ℝ in atTop, Quota X L W μ c o x j n l χ := by
  obtain ⟨m,hm⟩:= all_assess P Q; refine ⟨m,fun L hL X W μ c o hW hμ j n l χ=> ?_⟩
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact (radius_pay Q L l).mono fun x hx=>⟨hx,fun c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩
  obtain ⟨D,hd,hF,hX⟩:=he; obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j χ W hW μ hμ o l
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  filter_upwards [radius_pay Q L l,H,hg n 0 X.wanting X.reach,hK] with x he' h hh hA
  refine ⟨he',fun c f S T hW hx R I V hV=>?_⟩
  simp only [pow_zero,mul_one] at hh
  exact ⟨C,_,_,_,_,_,_,_,_,_,_,h c f S T (hW.patch hF hX) hx R _ I V hV,hA,(le_abs_self _).trans hh⟩
end hire

def Altitude (s : Sheet G) (K : MapPrices) {Q : Targets s K} (p : Expenses Q) (u : ℕ→ℕ) :=
  ∀ j i, StepStages j i → ∀ L:Side,u j ≤ L.val →∀ (W μ c:ℝ) (o: Target.Order G W), 0<W → 0<μ → ∀ k n l χ,
      ∀ᶠ x:ℝ in atTop, Quota (p j i) L W μ c o x k n l χ

theorem altitudes (s : Sheet G) (K : MapPrices) {Q} (p : Expenses (s:=s) (K:=K) Q) : ∃ u, Altitude s K p u := by
  choose m hm using fun i j=> quotas (Q i j)
  exact ⟨fromMax m, fun j i h L hL W μ c o he hV k n l χ=>hm _ _ _ ((le_fromMax m h).trans hL) _ W μ c o he hV k n l χ⟩

def Gates (Z : Delays Θ) := ∀ j x,Z.betaEntry j≤x→∀ i,StepStages j i → ∀ k:ℕ,k≤j → Quota (E j i) (D.L j) (f j i) (R.μ j i) (R.c j i) (R.o j i) x
    (s.profile i).order (s.profile i).power (High.countOrder k) Chi.canonical

theorem gates {u} (h : Altitude s K E u) (hu : ∀ j,u j ≤ (D.L j).val) (V : Delays Θ) :
    ∃ X : Delays Θ, DelayLe V X ∧ ∀ Y : Delays Θ, DelayLe X Y → Gates R Y := by
  have hp j i (hi : StepStages j i) : ∀ᶠ x:ℝ in atTop, ∀ k:ℕ,k≤j → Quota (E j i) (D.L j)
      (f j i) (R.μ j i) (R.c j i) (R.o j i) x (s.profile i).order (s.profile i).power (High.countOrder k) Chi.canonical:= by
    have hV : ∀ᶠ x:ℝ in atTop, ∀ k:Fin (j+1), Quota (E j i) (D.L j)
      (f j i) (R.μ j i) (R.c j i) (R.o j i) x (s.profile i).order (s.profile i).power (High.countOrder k.val) Chi.canonical :=
      eventually_all.mpr (fun k=> h j i hi (D.L j) (hu j) _ _ (R.c j i) (R.o j i) (R.consumes j i hi).1 (R.consumes j i hi).2.1 _ _ _ Chi.canonical)
    exact hV.mono (fun _ hx k hk=> hx ⟨k,Nat.lt_add_one_of_le hk⟩)
  obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> hp j i hi)
  exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hx i hi=> H j x ((h.beta _).trans hx) i hi⟩

section sharp
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P} {L : Side} {x W : ℝ} {n : ℕ}

def SpireGate (Q : ConnectedActivityE6.Target G P) (o : ConnectedActivityE6.Target.Order G W) (M : JointLoad.Heir.Record) (C : Libretto G n) (ε v : ℝ) (m p : ℕ) (κ : Chi) (L : Side) (x : ℝ) : Prop :=
  ∀ {c f : Side} {S : StepData c f} (T : Tube G S), Works P L x S T →
    ∀ (R : RG.Rep G f) (μ α : ℝ) (H : Cash W x μ L Q o α T R) (B : BudgetPoint),
    B.B=radiusB x → B.power=p → Plays C M B R.p P T x → Q.halo+ 5 ≤ m → Release.accepts m R.p.supportExponent ε L → Release.Quotation C p m R.p.supportExponent ε v →
    Lute.Plented C M B R.p L m x (gStep R.beta)→ ∀ j≥n, ∀ (C' d h Y A b r B₀ q : ℝ) (k : ℕ), Captain H j C' d h Y A b r B₀ q k Chi.canonical →
    ∀ (Z : ℕ→Prop) (v₀ : ℝ), (portion R.activities Z).EBound R.p v₀ → 0≤v₀ → v₀ ≤ incomingE G L x → ∀ q ε', Brim.Hired H Z M q κ Chi.canonical ε' B ε
      (v/L.val*v₀) ((L.val:ℝ)⁻¹*v₀)

lemma bookings (G : Gauge) (hG : G.Simple) (P : Teller G) (Q : ConnectedActivityE6.Target G P) (p : ℕ) (L:Side) {n : ℕ} (M : JointLoad.Heir.Record) (C : Libretto G n) (W ε v : ℝ) (o : ConnectedActivityE6.Target.Order G W) (m : ℕ) (κ : Chi)
    (hn : 2 ≤ n) (hM : M.ε≤1/4) (he : 0 ≤ ε) : ∀ᶠ s in atTop, SpireGate Q o M C ε v m p κ L s := by
  by_cases h : ∃ t : Patch,t.L=L ∧ t.J=P.j ∧ t.Branches P.bind G
  swap; · exact Eventually.of_forall fun s c f S T hh=> (h ⟨S.patch,hh.length_eq,hh.funds.atStep,hh.funds.kernel⟩).elim
  obtain ⟨D,h,hF,h'⟩:= h
  obtain ⟨X,hX,H⟩:= Brim.hired_policy G hG P L D h' p n C M hM hn Chi.canonical κ W o ε m he
  filter_upwards [eventually_gt_atTop (0:ℝ),H,hX.below (by norm_num) ((L.val:ℝ)⁻¹) (by positivity)] with x hx hh hE c' f S T hs R μ α H B hb hp hW hA hf hh' hu j hj C' d v' Y A b r B₀ q k N Z v₀ ht hv hV q' ε'
  obtain ⟨H',z',hz',hZ'⟩:=hh c' f S T (hs.patch h hF) hs R Q μ α H B hb hp hW hA v hf hh' hu _ hj A b d Y C' B₀ r v' q k N Z v₀ ht hV q' ε'
  exact ⟨H',z',fun i=> budget_loosen (hz' i) (mul_le_mul_of_nonneg_right hE hv),hZ'⟩

lemma buys_gold (G:Gauge) (L: Side):∀ᶠ x in atTop, Boulevard.gold G L x ≤ (L.val:ℝ)⁻¹ * incomingE G L x := by
  have ht : Rate G L (-(23/20)) (Boulevard.gold G L) := Rate.power
  filter_upwards [Delay.shift_pos G L,
    Sienna.contraction G L (a:=1) (b:=(L.val:ℝ)⁻¹) (by positivity) ht (show -(23/20:ℝ)< -(11/10) by norm_num)] with x hx hy
  have he : incomingE G L x=betaF G x L ^ (-(11/10):ℝ):= by
    unfold incomingE; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]; norm_num
  rw [he]; rw [one_mul] at hy; exact hy.le
end sharp


def Posted (z e : Return.Wages) (M : ℕ→ℕ→JointLoad.Heir.Record) (r : ℕ→ℕ→ℕ) (C : Programs s) (κ : ℕ→ℕ→Clockwork.Menu)
    (W : Delays Θ) := ∀ j x,W.betaEntry j ≤ x → ∀ i,StepStages j i → s.first ≤ i →
    SpireGate (Q j i) (R.o j i) (M j i) (C j i) (raise e j i) (z j i) (r j i) (s.profile i).power (Roof.wind κ j i)
      (D.L j) x ∧ Boulevard.gold G (D.L j) x ≤ ((D.L j).val:ℝ)⁻¹ * incomingE G (D.L j) x

lemma subscriptions (z e : Return.Wages) (r : ℕ→ℕ→ℕ) (C : Programs s) (κ : ℕ→ℕ→ Clockwork.Menu) (hG : G.Simple)
    (hM : ∀ j i,StepStages j i → s.first ≤ i → (M j i).ε ≤ 1/4) (ht : ∀ j i,0≤e j i) (V : Delays Θ) :
    ∃ W : Delays Θ, DelayLe V W ∧ ∀ X : Delays Θ, DelayLe W X → Posted R z e M r C κ X := by
  have hp j i (h : StepStages j i) : ∀ᶠ x in atTop, s.first ≤ i →
      SpireGate (Q j i) (R.o j i) (M j i) (C j i) (raise e j i) (z j i) (r j i) (s.profile i).power (Roof.wind κ j i)
        (D.L j) x ∧ Boulevard.gold G (D.L j) x ≤ ((D.L j).val:ℝ)⁻¹ * incomingE G (D.L j) x := by
    by_cases he : s.first ≤ i
    · filter_upwards [bookings G hG _ (Q j i) (s.profile i).power (D.L j) (M j i) (C j i) _ _ (z j i) (R.o j i) (r j i) _ (le_trans (by decide) (s.profile i).order_ge) (hM j i h he) (add_nonneg (ht j i) zero_le_two),buys_gold G (D.L j)] with x hx hh h₁; exact ⟨hx,hh⟩
    simp [he]
  obtain ⟨X,-,hv,hx⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (hp j)); exact ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hx'=>hx _ x ((h.beta _).trans hx')⟩

-- orientation fee constant negotiated pre-L

def advances (g : ℕ→ℝ) (z : Return.Wages) := ∀ j i, StepStages j i → away (s.profile i) * (z j i+2) / ((D.L j).val:ℝ) ≤ g i

lemma progresses (g : ℕ→ℝ) (h : ∀ i,0 < g i) (z : Return.Wages) (s : Sheet G) : ∃ k:ℕ → ℕ, ∀ L:ℕ→ℕ,k ≤ L → ∀ D:Rolls (ThroughLaunch.raise s L), advances (D:=D) g z := by
  let S (j i L : ℕ) : Prop := away (s.profile i) * (z j i+2) / (L:ℝ) ≤ g i
  have ht j i (_:StepStages j i): ∀ᶠ n in atTop,S j i n:= by
    refine (((tendsto_const_nhds (x:=away (s.profile i)*(z j i+2))).div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (h i))).mono ?_; exact fun n hh => le_of_lt (show _/(n:ℝ)<_ from hh)
  obtain ⟨X,-,_,Hx⟩:= collect_upper s.floorL _ (fun j=>eventually_transitions j _ _ (ht j))
  exact ⟨X,fun L hL D j i hi=> Hx j (D.L j).val ((hL _).trans (D.large j).need) i hi⟩

def zest (G : Gauge) (g : ℕ→ℝ) : Agenda G := fun _ D _ _ C z t r _ _ R _ _ _ M κ _ W =>
    Gates R W ∧ Posted R z t M r C κ W ∧ advances (D:=D) g z

lemma financed (hG : G.Simple) (g : ℕ→ℝ) (hg : ∀ i, 0 < g i) : (zest G g).Payable := by
  intro s T C z R E h
  obtain ⟨u,hU⟩ := altitudes s _ E
  obtain ⟨v,hV⟩ := progresses g hg z s
  refine ⟨u ⊔ v,fun L hh D f a J K _ _ p H hp θ V=>?_⟩
  obtain ⟨X,hX,hΓ⟩ := gates J (s:=ThroughLaunch.raise s L) (u:=u)
    (show Altitude (ThroughLaunch.raise s L) (UVExtension.Case.actualPay s T) E u from hU) (fun i=> ((sup_le_iff.mp hh).1 i).trans (D.large i).need) V
  obtain ⟨Y,hY,hK⟩ := subscriptions J z (Roof.rays s) mile C H hG hp (fun i j=> by unfold Roof.rays; have hz:=(s.profile j).price_pos; linarith) X
  exact ⟨Y,hX.trans hY,fun Z he=> ⟨hΓ _ (hY.trans he),hK _ he,hV L (sup_le_iff.mp hh).2 D⟩⟩
end YM.PhysicalNext.Repeat.Quests
