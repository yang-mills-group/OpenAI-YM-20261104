import YM.LocalLTE.Bonnet.Canopy
/-! Actual early path. One X after all choices. -/
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
open Progress.DirectedRecipe Extra.Histories Graces
variable (M: Preview H) {V:Bolt A} {p':ℕ}{κ d:ℝ}(g:G.Simple) (h:Canopy H M V) (hm:m<N)

-- Beacon actual POST outputs.Address full physical not just reach.
variable {U: Rep G (A.B.a.S.side (m+1) n)}
    (W:Rep G (A.B.a.S.side m n))
local notation "σ'"=> A.B.a.clock.op m n
local notation "K" => (p0:ℝ)+1-ε
structure Plot (hm:m<N) (U:Rep G (A.B.a.S.side (m+1) n)) (W:Rep G (A.B.a.S.side m n))
    (X': Guide A.B R.shape N m n U) (X₀:Urns.Expose (A:=A) (R:=R.shape) H.w U.beta N m) (k:ℕ)(G₀: Return.Wood A.B m n) (k': Return.Bookings A.B m n R.walls):Prop where
  coin : Opera.Price A.B R.shape N m n U X'
  inputLives : Lives A.B.bake N (m+1) n U
  inBand : U.beta∈band A.B.a (m+1)
  spring : W = Urns.baked H.w X' X₀ k -- explicit constructed logs/ledger. Prices downstream import
  holds : Urns.Firings H.w (M.maps N m hm) X' X₀ R.scout H.κ (H.d J I) k R.rider G₀ k'

variable (hp:Formed H M N m n W U)
include g hm hp
lemma at_plot : ∃ X' X₀ k G₀ k', Plot H M hm U W X' X₀ k G₀ k':=by
  obtain ⟨s,a,Q,F,h,f,k,hv,x,hx,rfl,rfl⟩:=hp
  have he:= F.ascend H hm g hv x hx (Opera.forum A.B R.shape); have hh:= F.literal H x hx (k:=k)
  rw [hh, ← show Q (F.holds.latch x)=Q x from (by rw [Embrasure.click _ x hx])]; let y:= F.holds.latch x; rw [f] at he
  exact ⟨F.hearth H x,F.exhibit H x,k,F.forest, _,F.holds.honors _, (F.turns _ y.2).1,(F.turns _ y.2).2,rfl,he⟩
omit hp
include h V
local notation "v₀"=> V.history N n
lemma scored : ∃ X₀ X' k G₀ k',Plot H M hm (V.history N n (m+1)) (V.history N n m) X₀ X' k G₀ k':=by exact at_plot H M g hm _ (h.held _ _ _ hm|>.1)
omit h V
variable {W}
variable {X':Guide A.B R.shape N m n U} {T': Urns.Expose (A:=A) (R:=R.shape) H.w U.beta N m} {G₀:Return.Wood A.B m n} {k':Return.Bookings A.B m n R.walls}
    (hx: Plot H M hm U W X' T' k G₀ k')
local notation "hero" => (postAncestor H.w X')
local notation "peg" => (postFog H.w (M.maps N m hm) X' T' H.κ (H.d J I) k)
local notation "χ'" => H.d J I
local notation "Δ" => mistΔ H.w (M.maps N m hm) X' T' H.κ (H.d J I) k
-- explicit costs for E labels; f rep with dummy K not used, only reg common.
local notation "E'"=> Magnet.traceE
local notation "X''"=> (M.maps N m hm)
local notation "P!" => (1/16+2*(1/16:ℝ))*Time.forecastE A.B.a m
include hx
lemma plotRead :
    let i:= gStep U.beta
    W.beta = U.beta + A.B.kin.alpha N m + royalty H.w X'' H.κ χ' i n + heirΔ H.w X'+ Δ ∧ W.activities.reg = (drawer G A₀).reg ∧ W.activities.E = printed H.w X'' H.κ χ' i n + postAncestor H.w X' + peg := by
  rw [hx.spring]; have he:= charted H.w (M.maps N m hm) X' T' g hx.holds
  exact ⟨he.1,(roll H.w X' T' (k:=k)).2.1,he.2⟩
lemma plotSpend :
    let K₁:= E' G A₀ (postAncestor H.w X'); let Y₁:= E' G A₀ (peg)
    let δ:=   gStep U.beta -- fix
    let i:= δ ^ ((p0:ℝ)+1-ε)
    K₁.RegularFamily (B) ∧ Y₁.RegularFamily (B) ∧ K₁.EBound B (Time.base G (A.B.a.params m) * (P!))∧
     Y₁.EBound B i∧ W.activities.KBound B (Real.sqrt (A.B.a.clock.forcedAllowance m) * i) ∧
     (B).threshold^2* |heirΔ H.w X'| ≤ (P!) ∧ (B).threshold^2 * |(Δ)| ≤ i:=by
  rw [hx.spring]; exact Urns.prices R.pledging hm H.w _ hx.inputLives hx.inBand X' _ g hx.holds H.due
omit g in
lemma counted (x:Config G (A₀)) :
    let f:= (A.B.a.clock.op m n).push U.beta U.eval
    f 1= Real.exp (W.v*Fintype.card (Site A₀)) ∧0<f 1 ∧ f x / f 1=({W with v:=0}:Rep G _).eval x:=by
  rw [hx.spring]; exact settle H.w _ X' T' hx.holds x -- may not need g
end YM.PhysicalNext.Repeat.Mallow
