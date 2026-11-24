import YM.QuadraticLocal.Tariff.Ticket
import YM.QuadraticLocal.Tariff.WalletS
import YM.QuadraticLocal.Relative.Palace
set_option autoImplicit false
noncomputable section

namespace YM.QuadraticLocal.Advent.Sycamore

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics

variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
variable {m n i b q k N:ℕ} (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "xd"=> Φ i
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
open Integration.LocalComparison VowsR QuadraticLocal.Mentor
variable {φ:ℕ→ℕ} (C:VowsR.LawScroll G φ) (Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)

namespace Locator
open Oak Tutoring Rebirth Rebirth.Scholar MintClock
open ThroughLaunch
open PaceR
open Shoot Coat

local notation "Λ"=> (Φ (i+1))
variable (hℓ:m≤ i) (hz: i<N)
local notation "hx"=> (show Burn.horizon k+2≤R.alloy.B.a.clock.J i from hk.trans ((S).fits.mono hℓ))
variable (V₁: Lesson (N:=N) R hk D Q π Γ hℓ)
local notation "Θ₁"=> V₁.entry
variable {U: RG.Rep G (R.family.side (i+1) n)}(e:ℝ)
    (hp:Lives (WheelP.neutral R.alloy).bake N (i+1) n U) (hw:U.beta∈ band R.alloy.B.a (i+1))
local notation "Wp"=> R.alloy.B.a.budget (i+1)
local notation "WI"=> R.alloy.B.a.budget i
local notation "I_"=> R.alloy.B.a.clock.J i
local notation "s_"=> R.metals.p.profile I_
local notation "γ"=> R.kit.v (R.alloy.B.a.clock.J (i+1)) I
local notation "L_"=> R.rolls.L Y
-- use the chosen path, not choosing new model epochs after n
local notation "Wt"=> Burn.Seed U (WheelP.M0 k 0 Wp (π (i+1)) U.beta)
variable (T₁: Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) U.beta))
variable (hT: Burn.Candor (R.alloy.B.a.budget (i+1)) U.activities (Set.range T₁.model) (Burn.silver ( R.alloy.B.a.clock.hatBeta (i+1))) e)
variable (K:Opera.Guide R.alloy.B R.kit.shape N i n U) (hc:Opera.Price R.alloy.B R.kit.shape N i n U K)
open Integration.LocalFormal Tree
variable (hP: Oak.Tutoring.Quarterly R D Q C Q0 Qa)(Ψp: WheelP.Certified R.alloy R.kit) (jJ:ℕ)(Hc μ:ℝ)(hD: Tracks.DrawVac jJ k Hc μ (R.alloy.B.a.clock.hatBeta (i+1)))

open QuadraticLocal.Sunday.Filing Rosary.Repair
variable (F₁: Forest (R.family.path.levels.clock.op i n).ratio)
-- use Commitment type.We.Checks.Member.Op.Weight before choosing ANY layout.St.
local notation "U₁"=> decoration U
local notation "Mu"=> ( (s_).clip )
local notation "φ⁺"=> (GoldN ) -- suppress
local notation "θ⁺"=> ( goldN D Q R.alloy hx V₁.entry U.beta )
local notation "Θ1"=> θ⁺-U.beta
local notation "γ₀"=> ( lead D Q R.alloy hx V₁.entry )
local notation "U₂"=> ( M0 k 0 WI γ₀ θ⁺ )
local notation "Wr"=> ( Time.forecastK (S) i (F).scout U.beta )
local notation "Wc"=> ( Time.quoteHard (S) i (F).book U.beta )
local notation "Yφ"=> ( WheelP.finalPrice s_ k L_ γ e Λ )
local notation "TCz"=> (WheelP.coefficientLoss s_ γ L_ Λ)

open AllOrder.Rosary.Guard.Dusk
variable (hσV:e ≤ AllOrder.High.serving ( R.alloy.B.a.clock.hatBeta (i+1) ))
variable (V:Locator.Calendar (N:=N) R hk D Q π Γ hℓ V₁ (U:=U) e F₁)
local notation "Q✧"=> (Locator.paneling R hk D Q π Γ hℓ V₁ V.listing V.source U.beta V.scalar)
local notation "Γℓ"=> ( Willow.haloSlack ((WI).B))

variable (Pt:QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
local notation "P"=> U
local notation "P'"=> ( Locator.paneling R hk D Q π Γ hℓ V₁ V.listing V.source U.beta V.scalar )
local notation "k0"=> V₁.entry
local notation "E!"=> (Oak.era R hk D Q π Γ hℓ Pt V₁)
local notation "G'"=> ( Coat.gStep U.beta )
local notation "FY"=> e
local notation "ℓ"=> (R.alloy.B.a.S.oneStep i n).exact_size
open RemainderComparison
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{Wx:Type}[Fintype Wx][DecidableEq Wx] {R₀: Marker.Census Wx}
open RG3 RG3.Annuncia
variable (u0: Θ→Wx)
local notation "S0"=> ( Replica u0 R₀ )
variable {K₁:Earn.Passport (R.family.side (i+1) n) Θ}
variable {W': Wx→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (A':∀ i, Set (W' i))(Kc:∀ i,Submodule ℝ (W' i))
local notation "Actors"=> (fun i=> A' (u0 i))
local notation "UK"=> (fun i=> Kc (u0 i))
variable (M:ι→ Earn.Row K₁ ( Replica u0 R₀ ) G ( Affinity.Wallet (fun i=> A' (u0 i)) ))
-- Warm height before projection.Room.Rep.URI* early. use exact η.L.Canonical user weights.Owner.Tx.T
variable (w0:Wx→ℝ)(ηL':Wx→ℕ)
local notation "w"=> ( w0 ∘ u0 )
local notation "ηL"=> ( ηL' ∘ u0 )
variable (Z₁:Tint.Incoming K₁ U ( Affinity.Wallet (fun i=> A' (u0 i)) ) ιw ( Replica u0 R₀ ))
local notation "ζ1"=> (Ψ i).p.supportExponent
open Cruise.Semester
local notation "S*"=> Pane.panel A i (ℓ)
local notation "Xn"=> ( S* )
-- no undocumented Φ viability required.Health.T.Art. Universe Hobby interior entire.F.No.
local notation "µ"=> (R.family.path.levels.clock.op i n).ratio
local notation "F₀"=> Cruise.publish
local notation "F₁'"=> (φ)
variable (Vh:ℕ)
variable (Vₜ:Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) jJ Pt.count Pt.stage k (R.alloy.B.a.clock.J i))
local notation "B*"=> U.p.B
local notation "κP"=> (K₁.coarser µ)
-- allow µ.Public alias L.Photo.ItemClock.A.Kernel.Run venue. 
local notation "Φout"=> (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i))
local notation "xΨ"=> Page
local notation "Ω"=> Oak.expenseReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh
local notation "pΩ"=> Oak.figureReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh
-- e-bound at normalized mark prices after actor arity packing.Frame.Pl.Q.Erank before masks.
variable (e_E c_P:ℝ) (heCp:c_P ≤ (Oak.expenseReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh)⁻¹)
-- max count. true layout hypotheses on row identity.Actor.Metadata.LabelSource.Policy
variable (hJ: Pt.count ≤ Burn.horizon k+2)(hv: Vh ≤ R.alloy.B.a.clock.J i)
variable (Yv: Earn.Scene.Armada M (w0 ∘ u0) (ηL'∘u0) (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) c_P jJ Pt.count Vh)
variable (hM:Earn.Tableau (fun i=> Kc (u0 i)) (fun i=> A' (u0 i)) M)(y: Affinity.Wallet (fun i=> A' (u0 i)))[Countable ι][Countable ιw]
variable (hL: Affinity.Taut K₁.support (fun i=> A' (u0 i)) (fun i=> Kc (u0 i)) Z₁.old)(hY: Affinity.Crown K₁.support (fun i=> A' (u0 i)) (fun i=> Kc (u0 i)) Z₁.hard)
variable (hO:Z₁.old.Paid (w0∘u0) U.p.B U.p.supportExponent e_E)(hP₁:Z₁.hard.Paid (w0∘u0) U.p.B U.p.supportExponent 1)
local notation "bP"=> (Mentor.Tuition.need jJ (Tolerance I))
local notation "tΩ"=> (Oak.student (n:=n) R hk D Q π Γ Q0 hℓ Pt V₁ Qa Actors M jJ Vₜ)
local notation "rΩ"=> Ω^5
local notation "ζc"=> ((pΩ).hitPrice G (µ).count (P).p (P').p c_P e_E FY G')
local notation "Θ'"=> (Mentor.Tuition.need jJ (Tolerance I))
namespace Elementary

open Earn
local notation "w₁"=> Stoop.radius w (Ω)
local notation "ξ₁"=> Ω⁻¹*c_P
local notation "eτ"=> Ω⁻¹*e_E
local notation "rμ"=> Pt.count
local notation "X₁"=> Earn.Earnings.hitPrice pΩ G (µ).count (P).p (P').p ξ₁ eτ FY G'
local notation "w★"=> ( Stoop.radius w (Ω^6) )
local notation "ν"=> (pΩ).fidelity
local notation "Y₁"=> (P').p.B
variable (he_C:c_P ≤ 1)(hV0:0<e_E)(ht₁:e_E≤1)
include hV0 he_C ht₁
open Affinity
local notation "K" => (Ω)
local notation "uA"=> ( Φ (i+1) )
set_option maxHeartbeats 660000
include V V₁ hP Ψp hp hw hσV g hz T₁ hT Vₜ hJ hv Yv hM y hL hY hO hP₁
local notation "uP"=> ( Mentor.Cruise.publish D R.rolls Q A φ Q0 Pt (E!) (ℓ) M jJ Vₜ k0)
local notation "θρ"=> ( Mentor.Cruise.funded D R.rolls Q A φ Q0 Pt (E!) (ℓ) M jJ Vₜ k0 V₁.studied Qa)

variable (ηz:ℝ) (s:ℕ)(hη:ηz ≤ 1/4)
variable (u: Quark.Stature R Pt.count s ηz i)(uB:Regency D R.rolls Q R.kit.target φ Q0 Qa R.alloy.delay)
local notation "IP"=> ( ((2:ℝ)*gStep U.beta)^(2*s) )
local notation "δ₀"=> forcedDivisor R.family i
local notation "κ"=> R.family.path.levels.clock.forcedAllowance i
local notation "rΦ"=> ( (jJ:ℝ)+1-ηz )
local notation "Kp"=> ( Quark.fidelity i jJ R )
local notation "Hw"=> ( max e_E Kp )
local notation "V_"=> ( (2:ℝ)^rΦ * (gStep U.beta)^rΦ )
local notation "K_"=> ( 8*Ω^(rμ+1)*(e_E+e) )
local notation "Due"=> ( K_+16*(V_) )
local notation "YT"=> (ε_Frame.Op_B) --unused
local notation "δ"=> ( (P').p.supportExponent )
local notation "Zp"=> ( Z )

local notation "Φw"=> Logarithmic R hk D Q π Γ Q0 Qa hℓ V₁ e jJ F₁ V Pt Actors UK M Z₁ w ηL Vh Vₜ Hw c_P -- expected see compile
variable {J:Type}
-- no implicit assumptions about q hats.True price-stage witness tenant(here)
local notation "Πγ"=> ( Delay.fineMonitor G L_ (Φ i) )

variable [Countable J] -- H.Countable.SuccessProof. references Mm.Body.
-- η witness any valid. Use ≤ at harmonic.Ar.As.Document.* needed. Canonical supports factorized.Compliant.
open Cruise.Semester
open Integration.LocalFormal Comparison.RG02
open Laurent Stationary AllOrder.Ink Fire Tree
open Marker Affinity Earn
open Kinetic.Port
local notation "T0"=> AllOrder.Floe.Step.tape (Burn.horizon k+2)
variable (Y₀:Step.PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
local notation "Hu"=> hP.employed
local notation "Tℓ" => ( Tint.Patrol.report tΩ )
local notation "Xy"=> (P')
local notation "Hr"=> ( Due + Ω^2 * c_P )
local notation "Θ_v"=> Semantic R hk D Q π Γ Q0 Qa hℓ V₁ e jJ F₁ V Pt Actors UK M Z₁ w ηL Vh Vₜ e_E c_P ηz s
local notation "ζ_1"=> ( P').p
variable (Yq:Tint.Incoming (K₁.coarser ( R.family.path.levels.clock.op i n ).ratio ) ( Locator.paneling R hk D Q π Γ hℓ V₁ V.listing V.source U.beta V.scalar ) (Affinity.Wallet (fun i=>A' (u0 i))) J ( Replica u0 R₀ ))
variable (hW0:e ≤ Hc*( Coat.gStep U.beta )^ ((jJ:ℝ)+1-μ)) (hε:0≤e_E)
local notation "Πκ" => ( Poker.Pay )
local notation "rough"=> (Due+K^rμ*(3*K+K^2))
variable (Sx:Set Θ)(hFull:Z₁.old.Paid (w0∘u0) U.p.B U.p.supportExponent 1) (hClean:(Deletion.sink Sx Z₁.old).Paid (w0∘u0) U.p.B U.p.supportExponent e_E)
open RG3 RG3.Annuncia
variable (Xb: Earn.Passport (R.family.side (i+1) n) Wx)(hXb:K₁=Tariff.clone u0 Xb)(hv0:∀ i,0<w0 i)
local notation "hXP"=> Tutoring.inherits R u0 Xb hXb
local notation "Xc"=> ( Xb.coarser µ )
local notation "Ξ"=> (Newhall R hk D Q π Γ Ψ Q0 Qa hℓ hz V₁ e T₁ jJ F₁ V Pt Actors UK M Z₁ w ηL Vh Vₜ e_E c_P ηz s Yq Sx)
local notation "E'"=> (P')
local notation "hΩ'"=> ( (pΩ).produce (µ).count )
-- Geometry Op.Word.Price Ω: deliberately charges at w0. Footprints in both projected and lifted Gallery on Arc: full behind every mask. Output sector(Sx) was certified on CLEAN unmodeled E budget e. Uses output actual projection of THIS realization of Semester chosen, retaining all γ weights simultaneously. See theorem Projection.Price.Frame.Amount.Read.`
local notation "Rr"=> ( rough )
local notation "tR"=> ( c_P )
local notation "L0"=> ( rendered M U.p (gStep U.beta) )
local notation "L_0"=> ( rendered tΩ (P').p (gStep U.beta) )
local notation "Zc"=> ((P').p.supportExponent+1+1)
local notation "Zi"=> (U.p.supportExponent)
local notation "P_EXP"=> ( min (Real.sqrt Wc) ( IP * δ₀ ) ) -- price and strongest at s: choose min proof. s≥1/ any. Use .both
structure Consulted :Prop where
     first : Ξ
     before : Tariff.WalletS.Recorded u0 R₀ w0 A' Kc L0 Z₁.old Z₁.hard Sx Zi 1 e_E (Ω*c_P) 1
     after : Tariff.WalletS.Recorded u0 R₀ w0 A' Kc L_0 Yq.old Yq.hard Sx Zc Rr Due (Ω^2*c_P) P_EXP
     for_mark (gA:Θ→ℂ)(A0:Θ→ℝ)(hR:∀ i,‖gA i‖ ≤ A0 i): Tariff.WalletS.Licensed (s:=Rr) (s1:=(Ω^2*c_P)) (a:=Zi) (b:=1) (c:=Ω*c_P) (a':=Zc) (t:=Due) (t1:=P_EXP) u0 R₀ w0 A' Kc Xb hXb gA A0 L0 Z₁.old Z₁.hard Sx e_E 1 Xc hXP L_0 Yq.old Yq.hard τ
     ritual (gA:Θ→ℂ)(A0:Θ→ℝ)(hR:∀ i,‖gA i‖ ≤ A0 i)(F':Forest (R.family.path.levels.clock.op i n).ratio)(t:(R.family.path.levels.clock.op i n).Choices)(u: Stationary.Link G (R.family.side i n))(v:Wallet A') : Tutoring.Ticket R hk D Q π Γ Q0 hℓ hz Pt V₁ Qa u0 A' M w0 ηL' jJ Vₜ c_P v F' t u gA A0 Xb hXb U E'
local notation "S_evt"=> (Consulted R hk D Q π Γ Ψ Q0 Qa hℓ hz V₁ e T₁ jJ F₁ V Pt u0 A' Kc M w0 ηL' Z₁ Vh Vₜ e_E c_P ηz s Yq Sx Xb hXb)
-- Calendar pre.B.Visibility.ScriptEngine.Location.Asset.Unit.Shape. Exposes even from untagged rolls.
open Tariff WalletS
omit hO hV0 hσV
variable (hNew: Newhall R hk D Q π Γ Ψ Q0 Qa hℓ hz V₁ e T₁ jJ F₁ V Pt (fun i=> A' (u0 i)) (fun i=> Kc (u0 i)) M Z₁ (w0∘u0) (ηL' ∘ u0) Vh Vₜ e_E c_P ηz s Yq Sx)
include hNew hFull hClean hv0 Sx
-- remove unused KC hV etc pre.Supplier.World 
omit hP Ψp g hT ht₁ he_C hJ hv hw
lemma enshrined : S_evt := by
    let hZ := hNew.semantic; let P₁:= hZ.tale; let hΩ:= P₁.Waffle; have h_0:0 ≤ c_P:= budget_nonneg (Yv.suggests 0); have h₂pos: 0≤ ( Ω ):= hΩ.paysAbove.le -- hx notation! replace
    have hT0 : 0≤ hΩ'*c_P:= budget_nonneg (P₁.earning.suggests 0);
    have hl : Recorded u0 R₀ w0 A' Kc L0 Z₁.old Z₁.hard Sx Zi 1 e_E (Ω*c_P) 1 := ⟨⟨⟨hL,hY⟩, hM.line U.p (gStep U.beta)⟩, hFull,hP₁, Lamps.loan_monotone _ ( Scene.Armada.paid M (w) ηL Yv _ hΩ.breeze ) (mul_le_mul_of_nonneg_right hΩ.wage h_0), hClean⟩
    have hT' : Recorded u0 R₀ w0 A' Kc L_0 Yq.old Yq.hard Sx Zc Rr Due (Ω^2*c_P) P_EXP:= by
       let hv: ( min (Real.sqrt Wc) ( IP * δ₀ ) )=( Real.sqrt Wc ) ∨ ( Real.sqrt Wc)> IP*δ₀:= by rcases le_or_gt (Real.sqrt Wc) (IP*δ₀) with h|h; exact Or.inl ( min_eq_left h ); exact Or.inr h
       refine ⟨ ⟨⟨P₁.repair,P₁.force⟩, P₁.school.line _ _⟩, hZ.tainted, ?_, Lamps.loan_monotone _ ( Scene.Armada.paid _ _ _ P₁.earning _ hΩ.soon ) ?_, hZ.connect ⟩
       · change Yq.hard.Paid w (P').p.B _ _; rcases hv with h|h; rw [h]; exact hZ.terrain.1; rw [min_eq_right h.le]; exact hZ.photographs
       apply (mul_le_mul_of_nonneg_right hΩ.quote hT0).trans; rw [pow_two,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΩ.earns h_0) h₂pos
    refine ⟨hNew, hl, hT', fun gA A0 hR=> ?_, fun gA A0 hR F' t u v=> ?_⟩
    · haveI : Countable (Scene.Texts M ((Xn).ratio) uP):= hNew.students; let YTexture := Scene.crewC M ((Xn).ratio) uP θρ; exact Tariff.WalletS.represented (ι:=Scene.Texts M ((Xn).ratio) uP) u0 R₀ w0 hv0 A' Kc Xb hXb gA A0 hR L0 Z₁.old Z₁.hard Sx e_E 1 hl Xc hXP L_0 Yq.old Yq.hard τ hT' hp.valid ((S).transition_mass ..) rfl (by linarith only []) (fun t=> ( hNew.semantic.tale.reads t ).symm) -- β exact op; ensure n.
    let v' := Tariff.draw u0 A' v; obtain ⟨hh₁,hh₂⟩:= (hNew.coherence F' t v')
    exact Tutoring.welcomes R hk D Q π Γ Q0 hℓ hz Pt V₁ Qa u0 A' M w0 ηL' jJ Vh Vₜ c_P v F' t u _ P₁.earning gA A0 hR hv0 Xb hXb U E' (hh₁ u) hh₂.reference₀ -- order hint `Vh ... ηZ` etc.
-- wrapper creates for old arbitrary.Can choose even when View.Owner.Meta.Document not allocated but α.Clock.Read.Resource.Curt.State.
include hv hJ Ψp g hT ht₁ he_C hP hD hW0 hε hη uB u hw v Y₀
omit hNew [Countable J] -- duplicates Countable J twice? structure intro loaded variable earlier.T.cur
set_option maxHeartbeats 900000
lemma consults : ∃ (J:Type) (_i:Countable J)(Yq:Tint.Incoming κP P' (Affinity.Wallet Actors) J S0), Consulted R hk D Q π Γ Ψ Q0 Qa hℓ hz V₁ e T₁ jJ F₁ V Pt u0 A' Kc M w0 ηL' Z₁ Vh Vₜ e_E c_P ηz s Yq Sx Xb hXb := by
    obtain ⟨J,hJ',Yq,h⟩:= Elementary.attends_New R g hk D Q π Γ Ψ v C Q0 Qa hℓ hz V₁ e hp hw T₁ hT hP Ψp jJ Hc μ hD F₁ V Pt Actors UK M Z₁ w ηL Vh Vₜ e_E c_P hJ hv Yv hM y hL hY hP₁ he_C ht₁ ηz s hη u uB Y₀ hW0 hε Sx hFull hClean
    exact ⟨ J,hJ',Yq, Elementary.enshrined R hk D Q π Γ Ψ Q0 Qa hℓ hz V₁ e hp T₁ jJ F₁ V Pt u0 A' Kc M w0 ηL' Z₁ Vh Vₜ e_E c_P Yv hM y hL hY hP₁ ηz s Yq Sx hFull hClean Xb hXb hv0 h ⟩ -- guess after omit
end Elementary
end Locator
end YM.QuadraticLocal.Advent.Sycamore
