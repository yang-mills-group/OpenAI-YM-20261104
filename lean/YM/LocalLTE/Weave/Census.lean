import YM.LocalLTE.FieldPT.Price
import YM.LocalLTE.Weave.Gate
/-! Requested-order public surface: strict local unmarked PT.Read types for conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Career
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals Averaging
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ}
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "R₀"=> A.B.kin.path N m
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe YM.LocalLTE Weft Scene
variable {p:ℕ} (W : Trail H p) (hm:m<N)
variable (k':ℕ)
local notation "L"=>D.L J
local notation "δ#"=> W.crew H m*radiusB x₀
local notation "tag" => Mallow.spread A.B.a N p n (m+1)
local notation "a₀"=> A.B.a.params m
local notation "ϑ"=> (F.school H W k' tag)
local notation "Ω"=> (F.billow H W k' tag)
variable (R':Rep G (A.B.a.S.side (m+1) n))(Φ:ℕ→ℝ→ Config G (A.B.a.S.side (m+1) n)→ℝ)
-- Calculator in regulator, independent of live/output densities. Curry early inputs first.
-- does NOT need x nor R'.
variable (r K:ℕ)
include F
lemma boughtCard: 3≤ (A.B.a.budget m).B:= by
    have hv:= F.hearth H 0|>.laws.data.room.sight; change 3 ≤ radiusB x₀; omega
local notation "π'"=> bandTotal K H.w W.κT J I
set_option quotPrecheck false
noncomputable def routePT (s:ℝ):= Price.operas ϑ B R₀ p (fun i=> Price.AtlasC.genes (F.dawnPT H W k' Φ i) s H.κ ((π') i) i r (Price.gallery R₀ B ϑ _ Ω (F.boughtCard H)))
noncomputable def routeKPT (s:ℝ):= Price.poloDelta ((π') p) r (F.kineticPT H W k' Φ p) s
section data
/- Analytic read-only: uses F but supplied Φ; changing funcs outside lower data does nothing. -/
variable (Ψ:ℕ→ℝ→ Config G (A.B.a.S.side (m+1) n)→ℝ)
lemma dlocal (τ:ℕ)(h:∀ i,(tag i) ≤ τ→ Φ i= Ψ i) : (F.corpus H W k' tag τ Φ)= (F.corpus H W k' tag τ Ψ):= by
    funext s; let X:= F.holds.base; let Δ:= Fan.vest (Q a) Φ s; let X41:= Fan.vest (Q a) Ψ s
    unfold Career.corpus Career.songPlan; rw [show East.way _ _ _ _ _ _ _ _ _ _= East.way (W.lease H m τ) X tag Chi.canonical p H.w.ℓ k' τ H.κ X41 from East.shield X p _ _ _ _ Δ X41 rfl rfl tag (fun i ht=> congr_fun (h i ht) s)]
lemma earlyPT (i:ℕ)(h:∀ (j:ℕ),(tag j) ≤ i → Φ j= Ψ j) : F.dawnPT H W k' Φ i= F.dawnPT H W k' Ψ i ∧ F.kineticPT H W k' Φ i= F.kineticPT H W k' Ψ i:= by constructor <;> funext s <;> simp only [Career.dawnPT, Career.kineticPT,F.dlocal H W k' Φ Ψ i h]
end data
section reads
variable (e ε':ℝ)(M:Preview H){R'}{V0 : Rep G (A.B.a.S.side m n)}{x:ℝ} (U: Peg H F W M k' r hm R' V0 x k) (hG:G.Simple)
local notation "B!"=> (betaF G x₀ L)
local notation "r#"=> (A.B.a.clock.forcedAllowance m)
local notation "Zf#"=> (A.B.a.clock.allowance m)
local notation "s#"=> (gStep R'.beta)
local notation "v#"=> ((gStep R'.beta)^(↑r+1:ℝ))
-- supplies all m across.Omega. insensitivity to lexer sorting explained in induction. Proof doc.
structure LeafQ (α β:ℝ)(P:ℕ→ℝ) (R':Rep G (A.B.a.S.side (m+1) n))(V0: Rep G (A.B.a.S.side m n)) : Prop where
   introD : DawnX p r R.target R.expense R.walls R.shape H.w H.d W.footprint W.κT (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.hatBeta m) H.κ ε' e K α β P
   supplyMeta : ∃ Φ:ℕ→ℝ→Pot G (A.B.a.S.side (m+1) n), Scene.Opens R' (Mallow.spread A.B.a N p n (m+1)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB x₀) p K H.κ α Φ ∧ Scene.Etched R' (Mallow.spread A.B.a N p n (m+1)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB x₀) p H.κ Φ
   predict (Φ:ℕ→ℝ→ Config G (A.B.a.S.side (m+1) n)→ℝ) (h: Scene.Opens R' (Mallow.spread A.B.a N p n (m+1)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB (A.B.a.clock.hatBeta m)) p K H.κ α Φ) : let s:= gStep R'.beta; let f:= F.routePT H W k' Φ r K; let θ:= F.routeKPT H W k' Φ r K; let v:ℝ:= (gStep R'.beta)^(↑r+1:ℝ); let u:= v+(s^e); (charged V0.activities (f s)).Valid B (Zf#+s^e) (Real.sqrt r#*v)∧ (charged V0.activities (V0.activities.E-f s)).Valid B u (Real.sqrt r#*v) ∧ |s^2*(V0.beta- (R'.beta+γ+θ s))| ≤ u -- reuse Career.industry with introD
-- does NOT assert adding charged activities.True K kept reference only.
variable {α β:ℝ}{P:ℕ→ℝ}
include hG U
lemma garner (D0:DawnX p r R.target R.expense R.walls R.shape H.w H.d W.footprint W.κT (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.hatBeta m) H.κ ε' e K α β P) : F.LeafQ H W k' r K e ε' α β P R' V0:= ⟨D0,F.predicts H W hm k' R' r K M U D0,fun Φ h=> F.authentic H W hm k' R' Φ r K M U hG D0 h⟩
end reads
end YM.PhysicalNext.Repeat.Mallow.Career
