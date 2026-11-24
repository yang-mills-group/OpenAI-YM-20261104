import YM.QuadraticLocal.Relative.Weave
import YM.QuadraticLocal.Perspective.Produce
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
variable (L0:Gallery α I o P R)(σw:V→ℝ)
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
variable [Countable I]
namespace Unfurl
open Tint Earn Affinity
variable {ℓ μ η J :Type} {X:Passport n V} [Countable ℓ]
variable {Xl:V→Type} [∀ i,AddCommGroup (Xl i)][∀ i, Module ℝ (Xl i)]
variable (Actors:∀ i,Set (Xl i))(uK:∀ i,Submodule ℝ (Xl i))
local notation "Wx"=> Affinity.Wallet Actors
variable (M:ℓ→ Row X R G (Affinity.Wallet Actors))(Y' : Tint.Incoming X P (Affinity.Wallet Actors) I R) (Sx:Set V) (y:Affinity.Wallet Actors)
local notation "K'"=> Patrol.picture M Y'
local notation "N'"=> (Patrol.picture M ( Unfurl.clean Y' Sx ))
variable {bM rM bU rU:ℝ} (U:Seal ( Tint.Patrol.picture M Y' ) σw bM rM) (T₁: Seal ( Tint.Patrol.picture M ( Unfurl.clean Y' Sx ) ) σw bU rU)
variable (hE:2*(bM+rM)≤K)(hU:2*(bU+rU)≤K)
variable (hC:∀ v:R.Mode,v.val.card≤k)
local notation "Lc"=> X.coarser S.ratio
variable (E:Lamps (Affinity.Wallet Actors) η G P'.p (X.coarser S.ratio).origin R)
variable (Eo: Lamps (Affinity.Wallet Actors) J G P'.p (X.coarser S.ratio).origin R)
variable [Countable η][Countable J] [Countable μ]
variable {δB σm δw:ℝ}
variable (D':Canopy.ShiftRows (Affinity.Wallet Actors) μ G P'.p (X.coarser S.ratio).origin R)
local notation "R0"=> Travel.raw H Iris K' σw U hw hx hE y
local notation "R1"=> Travel.raw H Iris N' σw T₁ hw hx hU y
variable (hM: Affinity.Collared X.support Actors uK P (Patrol.picture M Y'))
-- S unstamped CLEAN receipt, before Crop proof. Still actual or oriented dual. Provide on any inputs.
structure Stand (v:ℝ) (W:Travel.Walk H P' e f r s):Prop where
     price : Eo.Paid σw P'.p.B ( P'.p.supportExponent+1+1 ) v
     rights : Taut (X.coarser S.ratio).support Actors uK Eo
     shift : D'.Budget (Stoop.radius σw δw) P'.p.B ( P'.p.supportExponent+1 ) s
     scope : ∀ i U', Affinity.Stencil (X.coarser S.ratio).support Actors uK ( D'.place i ).val (fun t=> D'.soap t i U')
     patch : ∀ t U', (Travel.raw H Iris K' σw U hw hx hE y).log t U'= E.log t U'+Eo.log t U'+ D'.log t U'

lemma Clean (u: Stand (δw:=δw) H Iris σw hw hx Actors uK M (Unfurl.clean Y' Sx) y T₁ hU E Eo D' σm W): Arrangement H Iris σw hw hx Actors uK M Y' Sx y T₁ hU E Eo D' (δw:=δw) σm W:=⟨u.price,u.rights,u.shift,u.scope,u.patch⟩
end Unfurl
end Travel
end YM.QuadraticLocal
end

noncomputable section
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger Patrol
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b k τ:ℝ} {s i' j u i h : ℕ}
variable {Actor:V→Type} [∀ i, AddCommGroup (Actor i)] [∀ i,Module ℝ (Actor i)] (Actors:∀ i,Set (Actor i))(uK:∀ i,Submodule ℝ (Actor i))
variable (X:ι→Row P R G (Affinity.Wallet Actors)) (C:Club X)
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} (T:Incoming P U (Affinity.Wallet Actors) J R) (w:V→ℝ)(hw:∀ i,0<w i)
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Pressure
namespace Campus
open Lotus Merge
set_option quotPrecheck false
local notation "Y"=> Patrol.picture X T
variable (hq:HasSlots U.p U.activities) [Countable ι][Countable J]
variable (B:Travel.Seal (Patrol.picture X T) w b r) (y:(Affinity.Wallet Actors))
local notation "K"=> Club.Keys X C
local notation "P!"=> (Enroll.Weather X T w hw hq B)
local notation "S₀"=> (U.p.B)
local notation "Z"=> Coat.gStep U.beta
local notation "φ"=> Club.stamp X C
local notation "V₀"=> Club.troops X C
local notation "A₀"=> Patrol.Masks X
local notation "L₀"=> (Patrol.Shift X T)
variable (σ:Patrol.Signs X C)
local notation "e₀"=> (out X C T σ)
local notation "Π"=> (pulp X C T σ)
local notation "bT"=> (Patrol.enter X T)
local notation "MΓ"=> (brand (P!) y)
variable {D:Teller G}{W:ConnectedActivityE6.Target G D} {L:Side} {S:StepData c n} {A:Tube G S} {F:ConnectedActivityE6.Target.Order G a}
variable (H:Cash a e k L W F τ A U)
local notation "B*"=> radiusB e
local notation "O"=> Chi.canonical
local notation "q₀" => H.unionP
local notation "Xc"=> S.ratio.parent
local notation "E!"=> (Staff X T w hw hq B y H)
local notation "Tt"=> theater
local notation "Yo"=> (Campus.theater X T w hw hq B y H)
local notation "ϕ"=> Trigger.axis (Patrol.picture X T) w
local notation "Rt"=> Flues.candle P! y S
open Creek Seedlings BoxOf WickReps Mosaic Serif
variable (δ:ℕ)(Hp D0:ℕ)
variable {P':Burn.Locale G} (M0:Burn.Seed U P')(hβ: U.p.B≤2*radiusB e)
local notation "M"=> QuadraticLocal.Venue.Score.pose H M0 hβ
variable (p:Staff X T w hw hq B y H)
local notation "Sa"=> antiqueSet X T
local notation "Sb"=> outpost X T
namespace Hearth
variable {χ d d' V₁ V₂ B₀ b₁ χ' v' :ℝ}
variable {R':Rep G c}{m:ℕ}
variable (Q:Eyes H R' χ d d' χ' m) (hM: Investor.Medal X T w B V₁ V₂)
variable (A₁ A₂:ℝ)(hA:0<A₁)(hB:0<A₂)(ha:A₁≤1)(hb:A₂≤1)
open Muse
variable (hR: Hearth.Rooms (χ':=χ') (b:=b) (r:=r) A₁ A₂ V₁ V₂)
variable (hW:Sleet.cortex W.halo (Pressure.radiusB e) m Q.height 3 ≤ Hp) (hT:Hp ≤ D0)
variable (hK:∃ fv:ℕ→ℝ,Halo.Presents U (Set.range M0.model)ᶜ fv b₁ ∧ b₁ ≤ ConnectedActivityE6.incomingE G L e)
set_option quotPrecheck false
local notation "y₁"=> Campus.potential X T w hw hq B y H Hp D0 M0 hβ
local notation "Σ'"=> Campus.Batch X
local notation "f₀"=> Campus.concede X T w hw hq B y H D0 M0 hβ
local notation "Θ"=> (Q.pad)
local notation "σ₁"=> (Q.bells)
local notation "e₁"=> Campus.entry X T w hw hq B y H
local notation "A!"=> Campus.academy X T w hw hq B y H m
local notation "pu"=> (R'.p)
local notation "θ"=> (R'.p.supportExponent+1+1)
local notation "k₀"=> ((U.p).supportExponent)
local notation "Ψ"=> Set.range M0.model
local notation "Χ"=> Z^Q.height
local notation "OFee"=> (d'^m*d)
variable (X₁: ℝ) (hx:0<X₁) (Kc:Campus.Batch X→ℕ)
local notation "Kt"=> (fun i=> Rayon X Hp S U i)
local notation "u₀" k:max=> Hearth.surface X T w hw hq B y H Hp D0 M0 hβ k
local notation "Zℓ"=> (Hearth.league X T w hw hq B y H m)
local notation "s₁"=> (u₀ Kc)
local notation "Z₁"=> (Zℓ \ (s₁))
variable (hz:2*(b+r)≤ χ') (hm:∀ F:Club X,F.val.card≤ m)
local notation "Kp"=> Job X Hp S U
local notation "Work*"=> Perfor X T w hw hq B y H Hp D0 M0 hβ Kc
local notation "pilgrim"=> ride X T w hw hq B y H Hp D0 M0 hβ Kc
local notation "hxL"=> Travel.fiscal H Q Y w B hw hq hz y
local notation "Vd"=> (QuadraticLocal.Lanes.academy H O (Θ) P! y (fun _=>1) σ₁ hxL R'.p Q.block Q.pole le_rfl le_rfl)
variable (hV: WickReps.Manor.Spinal (Campus.theater X T w hw hq B y H) ((Hearth.league X T w hw hq B y H m) \ Hearth.surface X T w hw hq B y H Hp D0 M0 hβ Kc) (Flues.candle (Enroll.Weather X T w hw hq B) y S) R'.p (R'.p.supportExponent+1+1) X₁)
local notation "Co"=> (P.coarser S.ratio).origin
local notation "piS"=> (QuadraticLocal.Pane.Table (R:=R) Co Yo)
local notation "p₀"=> Primary X T w hw hq B y H m
local notation "q₁"=> Lefts X T w hw hq B y H Hp D0 M0 hβ Kc m
local notation "O!"=> QuadraticLocal.Pane.prepare Yo Set.univ ϕ
include hq hw hm
variable (v:Perfor X T w hw hq B y H Hp D0 M0 hβ Kc)
local notation "r₁"=> (v.fst)
local notation "j₀"=> (v.fst.val)
local notation "i₁"=> (v.snd.val)
local notation "K₁"=> Club.alliance X v.fst.val.1
local notation "ω"=> (Hearth.inner X T w hw hq B y H Q hz)
namespace Week
local notation "E₀"=> (Week.fuel X C σ)
local notation "χ₀"=> (Week.pack X C w)
variable (hy0:∀ i,(X i).Budget)
local notation "π₀" j:max=> Week.present X C T w hw hq B y σ H D0 M0 hβ j
variable (W': Press X j)(U': Width.Viewer X W' v' U.p.B)(X0:ℕ)
local notation "P₁"=> (Width.suite X C S.ratio W' U' Z)
local notation "Gx"=> (Club.roof X C S.ratio)
variable {g₀:ℝ} (hg:0≤g₀)(Law: Notice X T w hw hq B y H Hp D0 M0 hβ W' U' g₀ X0 (R':=R'))
variable (hL:D0≤X0)
local notation "Outp"=> neighbors X0 (Gx)
local notation "Ω"=> (pu).threshold
local notation "B0" => (Hearth.beck X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm)
local notation "U0"=> (P.coarser S.ratio)
open Next.Foundations AnalyticBridge VerifiedReset
variable (ZL: Week.Semester X T w hw hq B y H Hp D0 M0 hβ (R':=R') W' Kc U' g₀ X0)
namespace Semester
set_option quotPrecheck false
local notation "F'"=> fun k: Club X=> Club.alliance X k
variable (hS:Width.fuelCuts S.ratio.count U.p.B Hp R'.p.B X0)
local notation "Tx" jα:max=> ( Patrol.price X (jα).val.fst w (jα).val.snd )
local notation "si" jα:max=> neighbors X0 (Club.roof X (jα).val.fst S.ratio)
local notation "R0"=> (Week.Semester.portraits X T w hw hq B y H Hp D0 M0 hβ Kc W' U' X0 ZL hS)
local notation "Kc₁" k:max => (Campus.concede X T w hw hq B y H D0 M0 hβ k (Kc k))
variable (ht:Width.Together X C S.ratio U.p.B Hp)
local notation "ω'"=> (Hearth.inner X T w hw hq B y H Q hz)
local notation "Γ"=> (Club.alliance X C)
local notation "β₁"=> (Week.present X C T w hw hq B y σ H D0 M0 hβ)
local notation "pκ" s:max=> (Week.Semester.job X C Hp ht s)
variable {η_v:ℝ} (q:Press.Receipt X W' v' η_v)
local notation "w₀"=> (Campus.concede X T w hw hq B y H D0 M0 hβ)
variable (ρ:ℝ)(t:(Affinity.Wallet Actors)) (x:Config G c) (hp:Healthy R'.p.threshold (neighbors X0 (Club.roof X C S.ratio)) x)
local notation "Ψh"=> fun q:Patrol.Signs X C=> Week.fuel X C q t
local notation "C₁"=> (Width.audience X C S.ratio W' U' Hp)
namespace Curtain
open YM.QuadraticLocal.Shelter
local notation "U₀"=> Earn.Width.archive X S.ratio U.p.B Hp
local notation "G!"=> Earn.Width.Glass X S.ratio U.p.B Hp
local notation "f!"=> Earn.Width.famous X S.ratio W' q U' R'.p Hp ρ Z
local notation "cp" s:max=> (Week.pack X C w*Week.fuel X C s t:ℝ)
local notation "Z0" c:max=> (neighbors X0 (Club.roof X c S.ratio))
local notation "cp*"=> Week.Semester.portraits X T w hw hq B y H Hp D0 M0 hβ Kc W' U' X0 ZL hS
local notation "p₁"=> Perfor X T w hw hq B y H Hp D0 M0 hβ Kc
local notation "f0"=> (R'.p)
local notation "s0"=> (U.p.threshold)
local notation "Y2"=> (U.p.B)
local notation "A0" c:max=> (Club.alliance X c)
local notation "Ray*"=> (Curtain.rosette X T w hw hq B y H Hp D0 M0 hβ Kc W' U' X0 ZL hS)
local notation "Star*"=> (Curtain.sparkD X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm X0 hL)
local notation "ArtD"=> (Width.concerts X S.ratio W' q U' R'.p Hp X0 hS ρ Z)
local notation "Sp"=> (Curtain.sprout X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm W' U' X0 hL ZL hS q ρ)
local notation "Art"=> (Width.treasured X S.ratio W' q R'.p ρ Z)
local notation "Red"=> (Width.imagined X S.ratio W' q U' R'.p Hp ρ Z)
local notation "gl"=> Spire.convertGlobal T.old S R'.p
local notation "gl₀" => Spire.convertGlobal (Patrol.picture X T).E S R'.p
local notation "ζ"=> (fun i=> Rayon X Hp S U i)
local notation "bL₀"=> Hearth.rent X T w hw hq B y H Hp D0 M0 hβ X₁ Kc hV
local notation "g₁"=> Width.quiet X S.ratio R'.p Z
variable (σv:ℝ)
variable (hIndices : ∀ i : R.Mode, i.val.card ≤ m)
local notation "oFee"=> Spire.fees S.ratio.count (R'.p.supportExponent+1+1)
local notation "B₁"=> (R'.p.B)
variable {rM rL rP d₁ d₀ θ₁ : ℝ}
variable (hC:T.old.Paid w U.p.B U.p.supportExponent rM) (hArt : (Width.treasured X S.ratio W' q R'.p ρ (Coat.gStep U.beta)).Paid w R'.p.B (R'.p.supportExponent+1+1) rL)
   (hRed:(Width.imagined X S.ratio W' q U' R'.p Hp ρ (Coat.gStep U.beta)).Paid w R'.p.B (R'.p.supportExponent+1+1) rP)
variable (hCp:(Week.Semester.portraits X T w hw hq B y H Hp D0 M0 hβ Kc W' U' X0 ZL hS).Paid w R'.p.B (R'.p.supportExponent+1+1) d₁)
variable (hτ:∀ i: Earn.Width.Glass X S.ratio U.p.B Hp,(Lattice.coverNumber R'.p.B (neighbors X0 (Club.roof X i.val S.ratio)):ℝ) ≤ θ₁)
local notation "R₁"=> Curtain.ledger X T w hw hq B y H Hp D0 M0 hβ X₁ Kc hV W' U' X0 ZL hS q ρ
local notation "x_"=> t
local notation "hℓ"=> (show 0≤ θ from linarithE)
include Q hq hw
local notation "ey"=> (glyphBound _ _)
local notation "yv"=> (Hearth.themes_cost X T w hw hq B y H Q hz hIndices)
local notation "ae"=> (Wages)
local notation "χ1"=> oFee*rM+X₁+rP+d₁
local notation "xH"=> (show 0≤R'.p.supportExponent+1+1 from add_nonneg (add_nonneg R'.p.exponent_pos.le zero_le_one) zero_le_one)
local notation "Ψo"=> (Spire.pays T.old S w hw Q.cover xH U.p.exponent_pos.le hC Q.reach)
local notation "Ya"=> (Width.famous_paid X S.ratio W' q U' R'.p Hp ρ Z w hArt)
local notation "Zj"=> (Hearth.beck_cost X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm hIndices)
local notation "Ve"=> (Hearth.rent_cost X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hV hIndices)
local notation "Ho"=> ((Hearth.orient X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hm hV t x hIndices))
local notation "Y'"=> (Travel.raw H Q Y w B hw hq hz y)
set_option quotPrecheck false
set_option maxHeartbeats 600000
variable [Fintype V]
local notation "R!"=> (R'.p.supportExponent)
variable {uA uB tW : ℝ}
variable (uV: Travel.Walk H R' χ uA uB tW)
variable (r':ℝ)(hr':1 ≤ r') (hCoin: (r')⁻¹ * (Shelter.Deck.crewCost X0 (R'.p.supportExponent+1) θ₁*(d'^m*d+rL+d₁)) ≤ tW)
local notation "GΛ"=> (Earn.Width.Glass X S.ratio U.p.B Hp)
local notation "E_1"=> (Art).join R₁
local notation "Yw"=> (Stoop.radius w r')
local notation "SOL"=> (Travel.respondent H uV Q Y w B hw hq hIndices hz y Sp E_1)
namespace Ceremony
open Affinity Polish
variable (hX:Earn.Tableau uK Actors X)(hΛ:Affinity.Taut P.support Actors uK T.old)(htF:Affinity.Crown P.support Actors uK T.hard)
local notation "Zp" => Wallet Actors
local notation "X_"=> (P.coarser S.ratio).support
local notation "Up"=> S.ratio.parent ∘ P.origin
local notation "Mp"=> (Hearth.inner X T w hw hq B y H Q hz)
local notation "hY1"=> Ceremony.enchanted Actors uK X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hm hV W' U' X0 ZL hS q ρ hX hΛ htF
local notation "SX"=> ((Art).join R₁)
local notation "Sx"=> Static Actors uK R₁ X_
local notation "Q*"=> Ceremony.reveled Actors uK X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hm hV W' U' X0 ZL hS q ρ hX hΛ htF
local notation "E*"=> (effusion X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm W' U' X0 hL ZL hS q ρ hIndices uV Q*)
local notation "E!₀"=> (Art).join Q*
local notation "Univ"=> Ceremony.Senior Actors X T w hw hq B y H Hp D0 M0 hβ X₁ Kc hV W' U' X0 ZL hS q ρ
include Q hm hτ hCoin hr' hC hArt hRed hCp hIndices hX hΛ htF
-- Recover the primitive shift and EVERY used position/location/tag.Motion.We.Queue`. Returns even if P' not positive (World.Epoch.Queue_P.Alignment). Before post-lift budgets.
lemma earnings : Travel.Unfurl.Stand (δw:=r') H Q w hw hq Actors uK X T y B hz Art Q* Sp χ1 uV := by
    haveI:= carding X T w hw hq B y H Hp D0 M0 hβ Kc W' U' q (m:=m); let hP:= paidE X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hm hV W' U' X0 ZL hS q ρ hIndices hC hArt hRed hCp hz
    let hx := Affinity.Polish.costs Actors uK R₁ X_ hY1 hP; haveI : Countable {i// Univ i}:= inferInstance; refine ⟨hx, Affinity.Polish.tenancy Actors uK R₁ X_ hY1, ?_, ?_, ?_ ⟩
    · obtain ⟨f,hF,hH⟩:= (paidShift X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hm hV W' U' X0 hL ZL hS q ρ hIndices hC hArt hRed hCp r' hr' hτ).earned; exact ⟨f,hF,fun i=>budget_loosen (hH i) hCoin⟩
    · exact fun i x=> Ceremony.soaps Actors uK X T w hw hq B y H Hp D0 M0 hβ Q Kc hz hm W' U' X0 hL ZL hS q ρ x hX hΛ htF i
    intro t Uv; have he:= lines X T w hw hq B y H Hp D0 M0 hβ Q X₁ Kc hz hm hV W' U' X0 hL ZL hS q ρ t Uv hIndices hC hArt hRed hCp; have hh: (Q*).log t Uv=(R₁).log t Uv := Affinity.Polish.stems Actors uK R₁ X_ hY1 t Uv; change _= (Art).log t Uv + (Q*).log t Uv + ( Sp ).log t Uv; rw [hh]; exact he.trans (congr_arg ( · +(Sp).log t Uv) (Lamps.joinLog t Uv (hArt.sums xH hw ..) ( hP.sums xH hw ..))) -- parse
end Ceremony
end Curtain
end Semester
end Week
end Hearth
end Campus
end YM.QuadraticLocal.Tint
end
