import YM.LocalLTE.Key.Tend
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
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
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
-- Armor.Proofs only for now permit Need install at real calendars. Uniform after delays.
structure Adorn where
   revenue : ℕ→ℕ→ℝ
   M : ℕ→ℕ→ℕ→ℝ→ℝ
   spark (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥A.delay.betaEntry i→∀ k≤p, Urns.Straps D R.target H.w H.κ (H.d i j) x i j (W.footprint i j) k (M i j k x)
   receipts (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥A.delay.betaEntry i→∀ k≤p, Mallow.trophy (G:=G) (R.target i j|>.halo) (W.footprint i j) k (X.p.profile j) H.w (D.L i) x ≤ W.ψ i j*(betaF G x (D.L i))^(Pastel.chip (k+1))
   canopy (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥A.delay.betaEntry i → Price.Colors G (D.L i) (X.p.profile j) (Pane.cloak D i) p (W.ψ i j) (revenue i j) H.κ x (W.footprint i j*radiusB x) -- edit
namespace Career
local notation "Ω"=> F.hearth H
local notation "d'"=> W.crew H m*radiusB x₀
local notation "Q₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "t₀"=> (F.school H W k' tag)
local notation "V₀"=> (F.porch H W k' tag)
local notation "κ₀"=> H.κ
local notation "T₁"=> (Trio.resize H.w.ℓ (Rain.lint R.target A m))
local notation "S"=> (A.B.a.S)
local notation "u"=> W.hop H m
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe
local notation "Y"=> (W.crew H m)
variable (D': Adorn H W) (hk:F.Accepts H k)(hF:∀ x∈s, Trail.Hired H W (Q x) tag)
variable (x:ℝ)(hx:x∈s) (i:ℕ) (hi:i≤p)
include x hx hi D' hm F hk
set_option quotPrecheck false
local notation "fp"=> (gStep (F.codec H x).val)
lemma fireworks : 
    let q:= kiosk (preExponent (B)) Y*(ClockB.gust G L P T₁ H.w.l H.w.q x₀*Real.exp (Trio.stout P*coverTicket T₁))+ ((betaF G x₀ (D.L J))^Urns.dust i) * kiosk (preExponent B) Y
    Meadow.Budget B (leap d') (F.dapple H k x-F.glance H x i) q:=by
     intro t; have hu:= Trail.breadth H W (m:=m) (n:=n); have h':=(R.pledging.agenda _ _ (step_paid A.B.a m)).1; have ht':=F.turns _ (F.holds.latch x).2; have hp:=Urns.decency R.pledging hm ht'.1 ht'.2
     have hM:= (F.existZ H W).2; have hb:= hk x hx|>.2; let U:= F.exhibit H x
     have he':= Urns.tessera (n:=n) H.w hm H.paid.choose_spec R.inn H.vote R.pledging.jewels hp h' R.pledging.conducts.full U F.maps R.floor (R.settles _ _) hb
     let f₀:= F.dapple H k x; let f₁:= fun j:Site A₀=> Urns.inkO (κ:=H.κ) H.w F.maps (H.d J I) j (gStep (F.codec H x).val); let f' := F.glance H x i
     have hy:LocalLTE.Patch.light (c:=A₀) (Urns.Expose.read H.w U k) Q₀ (F.maps.reader H.w H.κ (H.d J I) fp)=f₀-f₁:=by funext i; unfold f₁; rw [Pi.sub_apply]; unfold LocalLTE.Patch.light Urns.inkO; simp only [sub_neg_eq_add]; rfl
     rw [hy] at he'; have he:= Trail.jumpPrice z d' Y (by omega) (le_refl _) _ he'
     have hC:= Urns.paysV H.w H.paid.choose_spec U F.maps Y (H.d J I) i hM hu.2.2 (D'.spark _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) _ hi) hm
     change Meadow.Budget _ _ (f₀-f') t; rw [show f₀-f'= (f₀-f₁)+(f₁-f') by abel]; exact Meadow.combineCost _ _ _ he hC -- expects Nat only?
include hF
local notation "f'"=>F.fruits H W k' tag x i
local notation "U"=>F.index H W k' tag k x
local notation "λs"=>u*(betaF G x₀ (D.L J))^(Pastel.chip (i+1))
lemma primordial (hX:Trail.Keeps H (F.hearth H x) tag p k') : Meadow.Budget B (t₀|>.reg) ((F.index H W k' tag k x).logRead -f') (2*u*(betaF G x₀ (D.L J))^(Pastel.chip (i+1))) :=by
    have ht:= F.cartons H W hm k' tag hk hF x hx hX _ hi; have hv:= F.fireworks H W hm D' hk x hx _ hi -- order
    obtain ⟨f,hp,h⟩:= Mallow.enter (V₀) B d' d' (Trail.histogram H W (F.hearth H x) tag k' i) _ _ _ ht hv (F.daily H W k' tag k x)
    refine ⟨f,fun i'=> budget_loosen (hp i') (?_),h⟩
    obtain ⟨hh,hB,hZ,hΨ⟩:= Rain.jersey (m:=m) (A:=A); rw [hΨ,(show preExponent B=Trio.stout (P) from congr_arg (·+3) hZ)]
    have hv:(trophy (G:=G) (Rain.lint R.target A m) (Y) i (P) H.w (D.L J) x₀) ≤ u * (betaF G x₀ (D.L J))^(Pastel.chip (i+1)):= D'.receipts _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) _ hi; unfold trophy at hv; linarith only [hv]
end Career
end YM.PhysicalNext.Repeat.Mallow
