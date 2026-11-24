import YM.QuadraticLocal.HaloMix.Yield
import YM.QuadraticLocal.HaloMix.Value
import YM.QuadraticLocal.Rough.Rove
/-! # Travel.Step.Generalized Replicas (not yet BUY)

 Receipts even for `kZ` arbitrarily large.IN.Persistence`

 `hΞ,prefix,purse` numeric (per-site proportional *local* traveler messages,
 including Θ). Hyp `Sh` (`Throng.Ledger`) asks for K marked-only cost in the
 same currencies AND layout. Occurrence proof; works at every test on ALL masked
 components including the true unmarked K partners. `prefix`: use `θ_B²` kind of
 geometry weights at any inherited epoch. Old Mark_E budget is b, Hard.Full
 hit at most b', while from its chosen ledger, nonzero marker words therein
 cost at most bMark; use that as inlet τ and pay roughly coupling/2 pow on K,
 absorbing it by supplying a much larger Ψ stencil for those K.Price.
 Portrait masks inherit.Index leases and continuation before true beta since
 Dynamo.Asset. Need buy on the actual trajectory.C.Calendar.Time.`. See HaloMix.

-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Progress.DirectedRecipe
open RemainderComparison
namespace Travel
variable {I V:Type}{G: Gauge}{n c L:Side}{x v e κ w a b d q z:ℝ}{α:Type*}
variable {A0:Teller G}{Q:ConnectedActivityE6.Target G A0}{Horizon:ConnectedActivityE6.Target.Order G w}
variable {S:StepData c n}{D:Pressure.Tube G S}{P:Rep G n}{P':Rep G c}
open ConnectedActivityE6
variable (H:Cash w x κ L Q Horizon z D P)
variable (E₀: ℕ→ RegularAddress c)(V₀:ℕ→ Config G c→ℝ) -- select unmarked first
open Lyric Muse Serif Spire Push.SectorMeasure
local notation "O"=> Chi.canonical
set_option quotPrecheck false
local notation "Ω"=> (Match.staple (H:=H) («J»:=H) rfl rfl rfl)
local notation "Xa"=> Refrain.read H Ω O E₀ V₀
variable {e f r s A B M Z : ℝ}
local notation "θ₀"=> P.p.supportExponent
local notation "θ₁"=> P'.p.supportExponent
local notation "p₁"=> P'.p
local notation "θ₂"=> (P'.p.supportExponent+1+1)
variable (W:Walk H P' e f r s)
local notation "ƒ"=> Spire.fees S.ratio.count θ₂
-- Aura recipe at a paid Horizon. D.clock answers EVERY load using Lamp cover; doesn't require model sup beyond `Bright`. `Ready` purchases at post calendar with arbitrary Root/Theta. Select s schedules for real occupancy clocks; budget tolerance in.Scale uses factor 2.
open Lotus
open Trigger Typeface GridRenewal.Rain
variable [DecidableEq V]{R:Marker.Census V}{o:V→Site n}
variable {Y Γ K : ℝ} {k k' : ℕ}
variable (Iris:Eyes H P' e Γ Y K k)
local notation "T"=> Type
-- choose pre-normalizing log-budget* before packing ANY disjoint types/pts. K & Krist input Hit sup T.P0. Can also choose for altered analytic model only.
variable (L0:Gallery α I o P R)(σw:V→ℝ)
variable {b b':ℝ}
variable (U:Seal L0 σw b b')
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
variable [Countable I]
local notation "A*"=> listCosts L0 σw hw hx U.supE U.crown (sighting L0 σw U) U.looks
local notation "z'"=> Trigger.axis L0 σw
variable {kZ:ℕ}(hC:∀ u:R.Mode,u.val.card≤kZ)(hE:2*(b+b')≤K)
local notation "pad'"=> Iris.pad
variable (u:α)
local notation "L★"=> fiscal H (P':=P') Iris L0 σw U hw hx hE u
local notation "Ψ"=> Trigger.choir L0 σw hw kZ hC
variable {bMark:ℝ}(Sh:Throng.Ledger L0 U bMark)
-- Specify core hLease via exact `estimates.card` (could also use root-specific
-- tighter p.Pre.Card but sufficient post-L site uniform). hpT and hT_b: one
-- higher boost Ξ_F on any nonquiet K. Supports boosts per occurrence not per
-- marker in the aperture test (good even for multiinput join and MANY roots). 
local notation "δM"=> 2*(b+bMark) -- used opportunity
local notation "evθ"=> Fintype.card (Site (S.ratio.count))
variable {ρs ζK:ℝ}(hpF:1≤ρs)(hΩ : (Y*ρs) * (2*(b+bMark)) ≤ K )(hKT:1≤ζK)(hΞ: ζK*(2*(b+bMark)) ≤ K)(hT : Halo.hike Q x (Fintype.card (Site (S.ratio.count))) (ζK*(2*(b+bMark))) ≤ Daisy.ribbon Q L x)
include Iris hE Sh
lemma magic {u':ℝ} (he:0 ≤ u')(w:u'*(2*(b+bMark))≤ K) : Motto (brand A* u) (Lyric.mulScale u' (fun _=>1)) 0 H θ₀ K Y (Eyes.sight Iris):= by
    let M:= Throng.estimates L0 S U Sh hw hx u
    let q := brand A* u; have hv:= Halo.scaled q (fun _=>1) M he
    refine ⟨?_,Iris.grant,le_rfl,by simp,by simp⟩
    exact ⟨Site n,inferInstance,id,(fun i=> (q i).crest), hv.currency,hv.pin, (fun i=>budget_loosen (hv.crown i) w), hv.tolerance.trans w, (fun j=> (parentCost S j).trans Iris.count)⟩
include hKT hT
lemma financeStar : Glit.LeasePlot (brand A* u) H (Lyric.mulScale ζK (fun _=>1)) Y θ₀ := by
    refine ⟨(evθ), (ζK*(2*(b+bMark))), ⟨?_, Iris.grant,le_rfl,by simp,by simp⟩, hT⟩
    exact ⟨Site n,inferInstance,id,(fun i=> (brand A* u i).crest), Halo.scaled (brand A* u) (fun _=>1) (Throng.estimates L0 S U Sh hw hx u) (zero_le_one.trans hKT)⟩
local notation "hp!"=> financeStar H Iris L0 σw U hw hx hE u Sh hKT hT
local notation "hΩt"=> Travel.magic H Iris L0 σw U hw hx hE u Sh (zero_le_one.trans (one_le_mul_of_one_le_of_one_le Iris.bells.allowed hpF)) hΩ
local notation "hskt"=> Travel.magic H Iris L0 σw U hw hx hE u Sh (zero_le_one.trans hKT) hΞ
lemma finance : Glit.LeasePlot (brand A* u) H (fun _=>1) Y θ₀:= Glit.LeasePlot.contract (brand A* u) H (Lyric.mulScale ζK (fun _=>1)) (hp!) (fun _=>1) (fun _=>zero_le_one) (fun _=>by unfold Lyric.mulScale; rwa [mul_one])
local notation "hCt"=> Travel.finance H Iris L0 σw U hw hx hE u Sh hKT hT
include W hC
local notation "Θ"=> S.ratio.parent ∘ o
local notation "ρ"=> W.entrance
local notation "Ξ"=> W.offer
local notation "Y0"=> Refrain.read H Ω O W.entrance W.offer
local notation "T!"=> Iris.bells
local notation "ℓ₀"=> Lanes.layoutGlobal H O pad' A* u (fun _ =>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ hCt (Trigger.colorCosting L0 S σw hx · p₁)
local notation "ℓ₁"=> Kiosk.First.led ℓ₀ W.first
local notation "M'"=> Creek.theater H O A* u (fun _=>1) Set.univ 0
local notation "μ"=> Lanes.tagged H A* u
local notation "μL"=> Lanes.honourL H O pad' A* u (fun _=>1) T! L★ p₁ Iris.block Iris.pole (le_refl _) (le_refl _) hpF hΩt
local notation "ƒL"=> QuadraticLocal.Pane.printBulbs Θ M' Set.univ z' μ (Flues.candle A* u S) μL
local notation "w₀"=> Spire.convertGlobal L0.E S p₁
local notation "β"=> (w₀).join ƒL
local notation "H'"=> L0.density
local notation "p0'"=> fun t=> S.push P.beta (TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S)
local notation "early"=> fun t=> S.push P.beta (H' t)
local notation "γ"=> Γ
omit Iris Sh hKT hT hE W hC in
include H in
private lemma isKernel : S.IsKernel P.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
variable [Fintype V]
include W hC hΩ hT hpF
-- keep `Head` registers unnormalized polynomial. pre & post attach use same marks.
local notation "X"=> ƒ*b+ρs⁻¹*Γ
lemma auction (s':Tree.Forest S.ratio) :
    (β).Paid σw P'.p.B θ₂ (ƒ*b+ρs⁻¹*Γ) ∧ (ℓ₁).Paid σw P'.p.B (θ₁+1) f ∧
      ReadZone α P'.p W.intermediate ℓ₁ early (β).log := by
    -- receipt
    have ha:0≤θ₂:= le_trans P'.p.exponent_pos.le (by linarith)
    obtain ⟨hV,hQ⟩:= Lanes.taking H O pad' A* u (fun _=>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ (le_refl _) (le_refl _) (show θ₁≤θ₂ from (by linarith)) hpF hΩt hCt (show _ from fun i=> Trigger.colorCosting L0 S σw hx i _) s'
    let δ := β; have hpL:= Spire.pays L0.E S σw hw Iris.cover ha P.p.exponent_pos.le (pays L0 σw U).budget Iris.reach
    have hδ : δ.Paid σw (p₁).B θ₂ X:= Lamps.joinPaid hpL hV
    refine ⟨hδ,?_⟩
    let K t:= TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S
    have hX t:= fiscal H Iris L0 σw U hw hx hE t
    have hi t: Integrable (K t) (prior G n):= Encore.oil (brand A* t) Set.univ (fun _=>1) z' H Ψ (hX t) -- countable ?
    have he:= Lanes.layoutGlobal_price H O pad' A* u (fun _=>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ hCt (Trigger.colorCosting L0 S σw hx · p₁)
    have hY := Spire.postGlobal S σw L0 K P'.p hQ b P.p.exponent_pos.le hw (pays L0 σw U).budget (isKernel H) hi (fun t U'=> Trigger.same L0 S σw hw hx U.supE U.crown (sighting L0 σw U) U.looks t U' H (hX t) Ψ (pays L0 σw U).budget P.p.exponent_pos.le) (fun t U=>Lamps.quiet_of_hasSum t U (hV.sums ha hw t U))
    have ht : (fun t (U:Config G c)=> globes L0 t+(ƒL).log t U) = (β).log:= funext fun t=> funext fun X'=>(show _ + _ = (β).log t X' from (by rw [Lamps.joinLog t X' (hpL.sums ha hw ..) (hV.sums ha hw ..), Spire.log S L0]))
    exact Kiosk.First.passes early (β).log ℓ₀ W.first hw (Hard.mono _ he Iris.room) (add_nonneg P'.p.exponent_pos.le zero_le_one) (ht ▸ hY)

section respond
variable {η ι:Type} [Countable ι][Countable η] (b₀:Canopy.ShiftRows α ι G P'.p (S.ratio.parent ∘ o) R)
   (K₀:Lamps α η G P'.p (S.ratio.parent ∘ o) R)
variable (hr:0≤ s) (hY:∀ U:Config G c,P'.eval U≠0) (hp:P'.eval=S.push P.beta P.eval)
include U u hw hx in
omit W hKT Sh hΩ hpF hT in
lemma tuneStill (t:α)(X₀:Config G c) : (S.push P.beta (L0.density t) X₀).part R.quiet= (Complex.ofReal (S.push P.beta P.eval X₀)) := by
    let f t' := TuneR (brand A* t') Set.univ (fun _=>1) 0 z' S; let q':= (pays L0 σw U)
    have he t' (V): L0.density t' V= cyclone (globes L0 t')*(f t' V) := Trigger.same L0 S σw hw hx U.supE U.crown (sighting L0 σw U) U.looks t' V H (fiscal H Iris L0 σw U hw hx hE t') Ψ q'.budget P.p.exponent_pos.le
    have ht: S.push P.beta (L0.density t) X₀= cyclone (globes L0 t)*S.push P.beta (f t) X₀:= by rw [funext (he t)]; exact Encore.moved (brand A* t) Set.univ (fun _=>1) z' H Ψ (Typeface.outputs H A* u t (fun _=>1) 0 L★) X₀ _
    have hq:= no_spark σw L0 P.p.exponent_pos.le hw b q'.budget t
    rw [ht, GridRenewal.Rain.passes (globes L0 t) hq,Poly.quiet_mul,Poly.pass_part _ hq,one_mul]; exact Lanes.tuneBlock H O pad' A* u t (fun _=>1) T! L★ z' Ψ X₀
def report : Gallery α η Θ P' R:= ⟨K₀,Kiosk.Second.canopy ℓ₁ b₀ W.second⟩
local notation "Ɓ"=> report H W Iris L0 σw U hw hx hC hE u Sh hKT hT b₀ K₀
include hY hp
set_option maxHeartbeats 600000 in
lemma successAll (s':Tree.Forest S.ratio)(hB:b₀.Budget σw P'.p.B (P'.p.supportExponent+1) s)
    (hK:K₀.Paid σw P'.p.B P'.p.supportExponent q)(h:∀ t U',(β).log t U'= K₀.log t U'+b₀.log t U'):
    (Ɓ).Pays σw P'.p.supportExponent q r ∧ (∀ t,S.push P.beta (L0.density t)=(Ɓ).density t) := by
    let δ := β; obtain ⟨hδ,hF,hQ⟩:= auction H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT s'; obtain ⟨hV,hP⟩:= Kiosk.Second.passes early (β).log ℓ₁ b₀ W.second hw P'.p.exponent_pos.le hF hB hQ K₀.log h (fun t U=>Lamps.quiet_of_hasSum _ _ (hK.sums P'.p.exponent_pos.le hw ..))
    exact ⟨⟨hK,hV⟩, upkeep _ P' K₀ _ hK P'.p.exponent_pos.le hw hP (fun t U'=> by rw [hp, tuneStill H Iris L0 σw U hw hx hC hE u]) hY⟩
omit Iris hKT Sh hΩ hT hpF W hC hE hY hp
omit [Fintype V] [Countable η] in
include hw in
private lemma loosen {n:Side}{PP:BudgetPoint}{oo:V→ Site n}{C:ℕ}{a':ℝ} (L:Lamps α η G PP oo R) (h:L.Paid σw C a b)(he:a'≤a): L.Paid σw C a' b:=by
 obtain ⟨f,hf,hF,hH⟩:=h.budget; exact ⟨f,hf,hF,fun x=>budget_mono (hH x) (fun i=>by split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hf _)) (Real.exp_nonneg _); exact le_rfl) (fun i=>by split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (mul_nonneg (Poly.worth hw _).le (hf _)); exact le_rfl)⟩

abbrev NamesFull := Waves L0.E ⊕ QuadraticLocal.Pane.Table (R:=R) Θ M' μ
private lemma staffFinite {ι:Type}[Countable ι] (M:ι→Leaf P): Countable (Sleet.Staff M H) := by
    -- adapt Abyss
    haveI : Countable (Head S):= Refrain.countSeeds
    unfold Sleet.Staff; haveI: Countable H.fragrances:= by unfold Cash.fragrances; infer_instance
    infer_instance
omit [Fintype V] in
lemma countF : Countable (NamesFull H L0 σw U hw hx u ) :=by -- missing Iris? NamesFull depends k but not Iris
   unfold NamesFull; haveI:= staffFinite H (brand A* u); infer_instance
include Iris Sh hKT W hC hE hr hY hp hpF hΩ hT

local notation "Lout"=> report H W Iris L0 σw U hw hx hC hE u Sh hKT hT (void (R:=R) G P'.p (S.ratio.parent ∘ o) α) β
def outAll := report H W Iris L0 σw U hw hx hC hE u Sh hKT hT (void G P'.p Θ α) β
lemma passedAll (s':Tree.Forest S.ratio) : (Lout).Pays σw P'.p.supportExponent (ƒ*b+ρs⁻¹*Γ) r ∧ (∀ t,S.push P.beta (L0.density t)=(Lout).density t):=by
   have h:= (auction H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT s').1
   haveI:= countF  H L0 σw U hw hx u
   refine successAll H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT (void G P'.p Θ α) β hY hp s' (void_paid (S:=S) (o:=o) (R:=R) (G:=G) (α:=α) σw s hr P'.p) (loosen σw hw β h ?_) ?_ -- generate
   · linarith
   intro t U; rw [Canopy.ShiftRows.log,tsum_empty,add_zero]

local notation "post"=> Throng.Hard.metal
include hΞ
omit hp hY
-- charged-only publication. Even at θ_cov+2 for QuadraticLocal.Log, full nonlinear mark K
-- strongly and through normalized post-Day.Price. Consume mask responders
-- separately through Pound.president (including induced marked-soft shifts).
lemma silhouette (s': Tree.Forest S.ratio) : (Lout).E.Paid σw P'.p.B θ₂ (ƒ*b+ρs⁻¹*Γ) ∧ (Throng.Hard.metal (Lout).K ζK).Paid σw P'.p.B θ₁ r := by
    have he:=(auction H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT s').1
    let L:= ℓ₀; let he':= Lanes.cash_mark H O pad' A* u (fun _=>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ hCt (Trigger.colorCosting L0 S σw hx · p₁) hKT hp! hskt
    let L':= (void G P'.p Θ α (R:=R)); let f':= ζK
    apply And.intro he; apply Throng.Hard.president L' W.second hw P'.p.exponent_pos.le hKT ℓ₁
    · exact Throng.Hard.through hKT W.first hw (add_nonneg P'.p.exponent_pos.le zero_le_one) ℓ₀ (Hard.mono (post L ζK) he' Iris.room)
    exact ⟨Empty.elim,fun i=>Empty.elim i,fun i=> budget_finite (fun i=>Empty.elim i) (by rw [Finset.univ_eq_empty,Finset.sum_empty]; exact hr)⟩
-- output directly on both budgets. Recovery of Θ expenses for unextracted
-- representation. This variant uses full-actor path; generally virtual ask separately.
include hY hp
set_option maxHeartbeats 450000 in
lemma broker (s': Tree.Forest S.ratio) :
    (Lout).E.Paid σw P'.p.B θ₂ (ƒ*b+ρs⁻¹*Γ) ∧ (Lout).Pays σw P'.p.supportExponent (ƒ*b+ρs⁻¹*Γ) r ∧ Throng.Hard.Pair (Lout).K σw P'.p.B θ₁ r (ζK⁻¹*r) ∧ ∀ t,S.push P.beta (L0.density t)=(Lout).density t:= by
    obtain ⟨h₁,h₂⟩:= silhouette H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hΞ hT hr s'
    let h₃:= passedAll H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT hr hY hp s'
    exact ⟨h₁,h₃.1,(Throng.Hard.Pair.theatre hKT hw (Lout).K h₂),h₃.2⟩

end respond
end Travel
end YM.QuadraticLocal
