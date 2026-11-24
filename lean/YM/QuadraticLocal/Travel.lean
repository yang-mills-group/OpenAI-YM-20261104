import YM.QuadraticLocal.Arrow
import YM.QuadraticLocal.Kiosk
/-!
# qlocal — marked call and response on this particular actual reclosure

Glue exact supplier, including budget-normalization and jointly processing NEW soft factors
if the connected log errors proof requests them. Build also works with empty interaction/populus.
This is for the whole polynomial, at ACTUAL vacuum. Positivity here is of that vacuum, useful
not just on good regions. This doesn't attempt a corresponding stronger claim on repeated test
locations without other budgets (branch footprint, shifts and all preimage geometry). Marker
price statements are fixed-load *prior* over any announced Θ. In particular don't infer post
budget from L1 estimates.

The porch carries unmarked data `Walk` first. So all captures use this precise construction even
across frame normalization. This ensures no circularity with vacuum vs packed Mark representations.
A/Q cycles are the given loops. Gauge invariance/support addresses of every Lamp certified before
connecting. `Snacks` & `FullBudget` adapters use this budget on THESE markers after moving, not
resumming into convenient new vacuum.

Here 
* α = parameter type, `Π unit` or booked rectangle of tests with Coupling/Root data fixed still.
* `s` = power of g asked in unnormalized compulsory seed; at least 1 when using reserve rates.
* `k` = multiplicity of allowed marker words; marker capacity hypotheses are EVERY mode ≤ that.
* `Θrails` = support reserve plus-two at the P0.Read Step; moving a mark mask before the SECOND
vacuum merger spends +1 reserve for the new masks; first merger is costed with NO mark-mask edits
(though it must carry *all* already marked K's). Width sup.
* `F(t)=S.push P.beta` ALWAYS, on actual same vacuum. Require that `P0.eval` equality is supplied
before this theorem. Binding to construction application subsequent. If you try extending to other
exact steps on perturbations without positivity everywhere, need strengthen `ReadZone` pay to give
actual multiplier alignment on flagged regions too (for which here positivity makes that automatic).
* `Receipt.Walk`: retains exactly the two actual vacuum mergers (Marlin and finish), layouts.
* `Sight`: Holds the output/step analytic supplier's exact `Eyes` and Moment budgets and reports a
pre-residual Rough, after Intake recertification from *only actual budget paid*. Exposes indicative
`First` & `Second canopy` records. Ready to align analytical model pre-Lamp, through `respond`;
any additive response computing a result with Paid *unk-body* and announcing a `ShiftRows` witness.
Unguaranteed formal jets aren't named in this file. (Needs to derive such comparison residual model
expressions AND pay their announced gains separately, to invoke with nonempty ShiftRows.)

Uses schedule conditions on Catalyst for the `Cash` actually making the call, including old pairing
`Refrain.read` with `E₀ V₀` and canonical `staple`, plus numerical gates for final reclosure MARK
allocation on true P0. The arbitrary punched mask layout is not cleaned in this module. These
aren't yet tied to construction weights on arbitrary mark cardinality: high caps here are set by
k before periods/deletions, and nonsharp larger-K-poly bounds need all-arity criterion pre-costed.
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
structure Walk (P':Rep G c)(e f r s:ℝ) where
    entrance : ℕ→RegularAddress c
    offer : ℕ→ Config G c→ℝ
    intermediate : Activities G c
    first : Kiosk.First P'.p (Refrain.read H Ω O entrance offer) intermediate e f (P'.p.supportExponent+1)
    second : Kiosk.Second P'.p intermediate P'.activities f r P'.p.supportExponent s
variable {e f r s A B M Z : ℝ}
local notation "θ₀"=> P.p.supportExponent
local notation "θ₁"=> P'.p.supportExponent
local notation "p₁"=> P'.p
local notation "θ₂"=> (P'.p.supportExponent+1+1)
variable (W:Walk H P' e f r s)
local notation "ƒ"=> Spire.fees S.ratio.count θ₂
-- Aura recipe at a paid Horizon. D.clock answers EVERY load using Lamp cover; doesn't require model sup beyond `Bright`. `Ready` purchases at post calendar with arbitrary Root/Theta. Select s schedules for real occupancy clocks; budget tolerance in.Scale uses factor 2.
open Lotus
structure Eyes (H:Cash w x κ L Q Horizon z D P)(P':Rep G c)(e V Y K:ℝ)(k:ℕ) where
    sight : ℕ
    extra : ℝ
    moves : ℝ
    σ : ℝ
    γ : ℝ
    thisLight : ℝ
    height : ℕ
    pad : Muse.Pad H P'.p.order O
    bells : Muse.Roles H O pad k height P'.p.power sight (P'.p.supportExponent+1+1) moves extra K σ Y V γ thisLight
    block : P'.p.B=radiusB x
    pole : P'.p.threshold=Pressure.temp x
    count : Fintype.card (Site S.ratio.count) ≤ sight
    cover : P.p.B ≤2*P'.p.B
    reach : 20*(P'.p.supportExponent+1+1)*Extra.Multi.tilePrice 0 ≤ (S.ratio.count.val:ℝ)*P.p.supportExponent
    grant : Lyric.radiusCost Q L P.p.supportExponent
    room : Real.exp ((-Q.mark L κ x)*(1/2:ℝ))*Coat.gStep P.beta^height ≤ e

open Trigger Typeface GridRenewal.Rain
variable [DecidableEq V]{R:Marker.Census V}{o:V→Site n}
variable {Y Γ K : ℝ} {k k' : ℕ}
variable (Iris:Eyes H P' e Γ Y K k)
local notation "T"=> Type
-- choose pre-normalizing log-budget* before packing ANY disjoint types/pts. K & Krist input Hit sup T.P0. Can also choose for altered analytic model only.
variable (L0:Gallery α I o P R)(σw:V→ℝ)
structure Seal (b b':ℝ) where
    supE : I→ℝ
    crown : ℕ→ Poly R
    perE i : 0≤ supE i
    coverage t i u (hu:u∈L0.E.ground i) : P.p.supBounds u (L0.E.ground i) (L0.E.nominal t i) (supE i)
    looks : ∀ i t U, Push.Corrected.Width.Covered (L0.K.hard t i U) (crown i)
    payment : Trigger.Payment (A':=L0) σw P.p.B P.p.supportExponent b b' supE crown
variable {b b':ℝ}
lemma sealed (h:L0.Pays σw P.p.supportExponent b b'): Nonempty (Seal L0 σw b b'):=by
    obtain ⟨f,hf,hP,hG⟩:=h.budget.budget; obtain ⟨s,hH,hC⟩:=h.wages.wages
    exact ⟨f,s,hf,(fun t i=>hP i t),hH,hG,hf,hC⟩
variable (U:Seal L0 σw b b')
include U in
lemma pays : L0.Pays σw P.p.supportExponent b b':= ⟨⟨U.supE,U.perE,(fun i t=> U.coverage t i),U.payment.bright⟩, ⟨U.crown,U.looks,U.payment.dusk⟩⟩
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
include U in
lemma sighting i t (V:Config G n): ‖L0.E.light t i V‖ ≤ U.supE i:= Lamps.light_size _ _ _ _ (U.coverage t i _ (L0.E.address i).anchor)
variable [Countable I]
local notation "A*"=> listCosts L0 σw hw hx U.supE U.crown (sighting L0 σw U) U.looks
local notation "z'"=> Trigger.axis L0 σw
variable (hC:∀ u:R.Mode,u.val.card≤k)(hE:2*(b+b')≤K)
local notation "pad'"=> Iris.pad
variable (u:α)
include Iris hE
lemma fiscal : Motto (brand A* u) (fun _=>1) 0 H θ₀ K Y (Eyes.sight Iris):= by
    let M:= Trigger.earned L0 S σw hw hx U.supE U.crown (sighting _ _ U) U.looks U.payment u
    have hh : 0≤2*(b+b'):= M.tolerance
    refine ⟨?_,Iris.grant,le_rfl,by simp,by simp⟩
    let q := brand A* u; refine ⟨Site n,inferInstance, id,(fun i=> (q i).crest), M.currency,M.pin, (fun i=>budget_loosen (M.crown i) hE),hh.trans hE, (fun j=> (parentCost S j).trans Iris.count)⟩
local notation "L★"=> fiscal H (P':=P') Iris L0 σw U hw hx hE u
local notation "Ψ"=> Trigger.choir L0 σw hw k hC
include W hC
local notation "Θ"=> S.ratio.parent ∘ o
local notation "ρ"=> W.entrance
local notation "Ξ"=> W.offer
local notation "Y0"=> Refrain.read H Ω O W.entrance W.offer
local notation "T!"=> Iris.bells
local notation "ℓ₀"=> Lanes.layoutK H O pad' A* u (fun _ =>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ (Trigger.colorCosting L0 S σw hx · p₁)
local notation "ℓ₁"=> Kiosk.First.led ℓ₀ W.first
local notation "M'"=> Creek.theater H O A* u (fun _=>1) Set.univ 0
local notation "μ"=> Creek.Academy H O A* u (fun _=>1) Set.univ 0 k
local notation "μL"=> Lanes.academy H O pad' A* u (fun _=>1) T! L★ p₁ Iris.block Iris.pole (le_refl _) (le_refl _)
local notation "ƒL"=> QuadraticLocal.Pane.printBulbs Θ M' Set.univ z' μ (Flues.candle A* u S) μL
local notation "w₀"=> Spire.convertGlobal L0.E S p₁
local notation "β"=> (w₀).join ƒL
local notation "H'"=> L0.density
local notation "p0'"=> fun t=> S.push P.beta (TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S)
local notation "early"=> fun t=> S.push P.beta (H' t)
local notation "γ"=> Γ
omit Iris hE W hC in
include H in
private lemma kernel : S.IsKernel P.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
variable [Fintype V]
-- keep `Head` registers unnormalized polynomial. pre & post attach use same marks.
local notation "X"=> ƒ*b+Y^k*Γ
lemma docket (s':Tree.Forest S.ratio) :
    (β).Paid σw P'.p.B θ₂ (ƒ*b+Y^k*Γ) ∧ (ℓ₁).Paid σw P'.p.B (θ₁+1) f ∧
      ReadZone α P'.p W.intermediate ℓ₁ early (β).log := by
    -- receipt
    have ha:0≤θ₂:= le_trans P'.p.exponent_pos.le (by linarith)
    obtain ⟨hV,hQ⟩:= Lanes.takes H O pad' A* u (fun _=>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ (le_refl _) (le_refl _) (show θ₁≤θ₂ from (by linarith)) (show _ from fun i=> Trigger.colorCosting L0 S σw hx i _) s'
    let δ := β; have hpL:= Spire.pays L0.E S σw hw Iris.cover ha P.p.exponent_pos.le (pays L0 σw U).budget Iris.reach
    have hδ : δ.Paid σw (p₁).B θ₂ X:= Lamps.joinPaid hpL hV
    refine ⟨hδ,?_⟩
    let K t:= TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S
    have hX t:= fiscal H Iris L0 σw U hw hx hE t
    have hi t: Integrable (K t) (prior G n):= Encore.oil (brand A* t) Set.univ (fun _=>1) z' H Ψ (hX t) -- countable ?
    have he:= Lanes.layoutK_price H O pad' A* u (fun _=>1) T! L★ H Ω p₁ Iris.block Iris.pole ρ Ξ z' Ψ (Trigger.colorCosting L0 S σw hx · p₁)
    have hY := Spire.postGlobal S σw L0 K P'.p hQ b P.p.exponent_pos.le hw (pays L0 σw U).budget (kernel H) hi (fun t U'=> Trigger.same L0 S σw hw hx U.supE U.crown (sighting L0 σw U) U.looks t U' H (hX t) Ψ (pays L0 σw U).budget P.p.exponent_pos.le) (fun t U=>Lamps.quiet_of_hasSum t U (hV.sums ha hw t U))
    have ht : (fun t (U:Config G c)=> globes L0 t+(ƒL).log t U) = (β).log:= funext fun t=> funext fun X'=>(show _ + _ = (β).log t X' from (by rw [Lamps.joinLog t X' (hpL.sums ha hw ..) (hV.sums ha hw ..), Spire.log S L0]))
    exact Kiosk.First.passes early (β).log ℓ₀ W.first hw (Hard.mono _ he Iris.room) (add_nonneg P'.p.exponent_pos.le zero_le_one) (ht ▸ hY)

section respond
variable {η ι:Type} [Countable ι][Countable η] (b₀:Canopy.ShiftRows α ι G P'.p (S.ratio.parent ∘ o) R)
   (K₀:Lamps α η G P'.p (S.ratio.parent ∘ o) R)
variable (hr:0≤ s) (hY:∀ U:Config G c,P'.eval U≠0) (hp:P'.eval=S.push P.beta P.eval)
def raw := β
def mid := ℓ₁
local notation "read*"=> raw H Iris L0 σw U hw hx hE u -- no W or k?
local notation "mid†"=> mid H W Iris L0 σw U hw hx hC hE u
include U u hw hx in
omit W in
lemma tuneQuiet (t:α)(X₀:Config G c) : (S.push P.beta (L0.density t) X₀).part R.quiet= (Complex.ofReal (S.push P.beta P.eval X₀)) := by
    let f t' := TuneR (brand A* t') Set.univ (fun _=>1) 0 z' S; let q':= (pays L0 σw U)
    have he t' (V): L0.density t' V= cyclone (globes L0 t')*(f t' V) := Trigger.same L0 S σw hw hx U.supE U.crown (sighting L0 σw U) U.looks t' V H (fiscal H Iris L0 σw U hw hx hE t') Ψ q'.budget P.p.exponent_pos.le
    have ht: S.push P.beta (L0.density t) X₀= cyclone (globes L0 t)*S.push P.beta (f t) X₀:= by rw [funext (he t)]; exact Encore.moved (brand A* t) Set.univ (fun _=>1) z' H Ψ (Typeface.outputs H A* u t (fun _=>1) 0 L★) X₀ _
    have hq:= no_spark σw L0 P.p.exponent_pos.le hw b q'.budget t
    rw [ht, GridRenewal.Rain.passes (globes L0 t) hq,Poly.quiet_mul,Poly.pass_part _ hq,one_mul]; exact Lanes.tunePush H O pad' A* u t (fun _=>1) T! L★ z' Ψ X₀
-- second step; canopy on true P. offsets & test estimates can assert literal Link.
def respondent : Gallery α η Θ P' R:= ⟨K₀,Kiosk.Second.canopy ℓ₁ b₀ W.second⟩
local notation "Ɓ"=> respondent H W Iris L0 σw U hw hx hC hE u b₀ K₀
include hY hp
omit hY hp [Countable η] in
set_option maxHeartbeats 200000 in
lemma success [Countable η]
    (b₀ : Canopy.ShiftRows α ι G P'.p (S.ratio.parent ∘ o) R)
    (K₀ : Lamps α η G P'.p (S.ratio.parent ∘ o) R)
    (hY : ∀ U, P'.eval U ≠ 0) (hp : P'.eval = S.push P.beta P.eval) (s':Tree.Forest S.ratio)(hB:b₀.Budget σw P'.p.B (P'.p.supportExponent+1) s)
    (hK:K₀.Paid σw P'.p.B P'.p.supportExponent q)(h:∀ t U',(β).log t U'= K₀.log t U'+b₀.log t U'):
    ((respondent H W Iris L0 σw U hw hx hC hE u b₀ K₀)).Pays σw P'.p.supportExponent q r ∧ (∀ t,S.push P.beta (L0.density t)=((respondent H W Iris L0 σw U hw hx hC hE u b₀ K₀)).density t) := by
    let δ := β; obtain ⟨hδ,hF,hQ⟩:= docket H W Iris L0 σw U hw hx hC hE u s'; obtain ⟨hV,hP⟩:= Kiosk.Second.passes early (β).log ℓ₁ b₀ W.second hw P'.p.exponent_pos.le hF hB hQ K₀.log h (fun t U=>Lamps.quiet_of_hasSum _ _ (hK.sums P'.p.exponent_pos.le hw ..))
    exact ⟨⟨hK,hV⟩, upkeep _ P' K₀ _ hK P'.p.exponent_pos.le hw hP (fun t U'=> by rw [hp, tuneQuiet H Iris L0 σw U hw hx hC hE u]) hY⟩
omit Iris W hC hE hY hp [Fintype V] in
include hw in
omit [Countable η] in
private lemma weaker {n:Side}{PP:BudgetPoint}{oo:V→ Site n}{C:ℕ}{a':ℝ} (L:Lamps α η G PP oo R) (h:L.Paid σw C a b)(he:a'≤a): L.Paid σw C a' b:=by
 obtain ⟨f,hf,hF,hH⟩:=h.budget; exact ⟨f,hf,hF,fun x=>budget_mono (hH x) (fun i=>by split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hf _)) (Real.exp_nonneg _); exact le_rfl) (fun i=>by split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (mul_nonneg (Poly.worth hw _).le (hf _)); exact le_rfl)⟩
omit Iris W hC hE hY hp
-- instantiate to empty Shifts with zero spool

def void (G:Gauge)(p:BudgetPoint)(o:V→Site c)(α:Type*):Canopy.ShiftRows α Empty G p o R:= ⟨Empty.elim,fun _=>Empty.elim,fun _ i=>Empty.elim i,fun _ i=>Empty.elim i, fun _ i=>Empty.elim i,fun _ i=>Empty.elim i⟩
omit [Fintype V] in
lemma void_paid (s:ℝ)(hs:0 ≤ s)(P:BudgetPoint) : (void (o:=Θ) G P α (R:=R)).Budget σw P.B (P.supportExponent+1) s := ⟨Empty.elim,fun i=>Empty.elim i,fun i=> budget_finite (fun i=>Empty.elim i) (by rw [Finset.univ_eq_empty,Finset.sum_empty]; exact hs)⟩ -- simp Finset? fix
-- Small domain statuses from explicit θ metadata
abbrev Names := Waves L0.E ⊕ QuadraticLocal.Pane.Table (R:=R) Θ M' μ
-- passthrough instance with unfolded 
private lemma staffCount {ι:Type}[Countable ι] (M:ι→Leaf P): Countable (Sleet.Staff M H) := by
    -- adapt Abyss
    haveI : Countable (Head S):= Refrain.countSeeds
    unfold Sleet.Staff; haveI: Countable H.fragrances:= by unfold Cash.fragrances; infer_instance
    infer_instance
omit [Fintype V] in
lemma counting : Countable (Names H L0 σw U hw hx u (k:=k)) :=by -- missing Iris? Names depends k but not Iris
   unfold Names; haveI:= staffCount H (brand A* u); infer_instance
include Iris W hC hE hr hY hp
local notation "Lout"=> respondent H W Iris L0 σw U hw hx hC hE u (void (R:=R) G P'.p (S.ratio.parent ∘ o) α) β
def outcome := respondent H W Iris L0 σw U hw hx hC hE u (void G P'.p Θ α) β
lemma passed (s':Tree.Forest S.ratio) : (Lout).Pays σw P'.p.supportExponent (ƒ*b+Y^k*Γ) r ∧ (∀ t,S.push P.beta (L0.density t)=(Lout).density t):=by
   have h:= (docket H W Iris L0 σw U hw hx hC hE u s').1
   haveI:= counting (k:=k) H L0 σw U hw hx u
   refine success H W Iris L0 σw U hw hx hC hE u (void G P'.p Θ α) β hY hp s' (void_paid (S:=S) (o:=o) (R:=R) (G:=G) (α:=α) σw s hr P'.p) (weaker σw hw β h ?_) ?_ -- generate
   · linarith
   intro t U; rw [Canopy.ShiftRows.log,tsum_empty,add_zero]
end respond
end Travel
end YM.QuadraticLocal
