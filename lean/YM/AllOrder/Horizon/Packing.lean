import YM.AllOrder.Horizon.Local
/-!
# Budget at ALL eligible shutters

Across immutable `Factor` no relifting proofs at a given β. Poly-period powers schedule receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} (A : Alloy X D) (F: Factor A) {c f : Side} {m n N : ℕ}
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
set_option quotPrecheck false
local notation "W" => (A.B.a.params m).clip
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)

variable {η : ℕ→ℕ→ℝ} (H : Lodge D F.shape η A.delay)
variable {β : ℝ} (π:f.val=c.val*(A.B.a.S.block m).val) {U:RG.Rep G f} (Z': Chartlet F.shape A N m π U) (hz:SeekR F.shape A N m π Z') (hm:m<N)
local notation "S'" => Pane.panel A m π
local notation "Σ₀" => orchestra A N π
local notation "V₁" => (A.B.a.budget (m+1))
local notation "χ" => Chi.canonical
local notation "Y₀" => (F.shape.o J I|>.K)
include hm Z'
lemma issued {K: Forest (Pane.panel A m π).ratio} (_hU:U=virgin (Pane.orchestra A N π) (A.B.a.budget (m+1)) β) (hf:c.val ≤ most Y x₀): Quilt Σ₀ K (Trio.paySide G L Y x₀) := Function.const _ (by
  exact Trio.quilt G L Y x₀ S' (Σ₀) K hf (PriceCompiler.block_eq A.B.valid m) Z'.laws.data.room.larger
  ) hm
include H Z'
lemma desk {K: Forest (Pane.panel A m π).ratio} (hU:U=virgin (Pane.orchestra A N π) (A.B.a.budget (m+1)) β) (hf: c.val ≤ most Y x₀) : ∃ ρ:Bid.Dir G c→AxisChart G K,
    Critical K (Σ₀).high (Σ₀).up ρ ∧ ClassicalMatch K (Σ₀).high (Σ₀).low (Σ₀).up (Σ₀).down ρ∧
    ∀ (k:ℕ) (x:Positions (Uniform.Primary c G)), k≤ I → flags (Pressure.temp x₀) (actual x)=∅ → ‖x‖+2*furl G L x₀<eaves G L x₀→∀ (l:(S').Choices) (r:ℝ), ‖(gStep β,x)‖ ≤ r → r < eaves G L x₀ →
    0<Token.tramp Σ₀ V₁ β x∧ Brush ((E).order+I+3) (z^(η J I)*(z*r^(k+3)+r^(k+1))+ z^(seam_hat I)) r⁻¹ (Token.pures (Σ₀) V₁ β- Local.Pure.script K Σ₀ X.O ρ β l k) x := by
  subst U
  have hF (n : ℕ): 0≤ n:= Nat.zero_le _
  have he : Quilt Σ₀ K (Trio.paySide G L Y x₀):= issued A F π Z' hm rfl hf
  let Z:= P; let B':= A.B.a.clock; let f j i x : ℝ:= Trio.paySide G (D.L j) (parking (tall i) (F.target j i|>.halo)) x; let S:= S'
  obtain ⟨ρ,hρ,hK,hY⟩:= presents D A («Y»:=f) (Factor.floor F) hm π K he; refine ⟨ρ,hρ,hK,fun k x hk hx hx' l r hr hB=>?_⟩
  have ht:MorningP D R I J k ((E).order+I+3) x₀ (η J I):=(lot A F H).script k hk
  let X':= Greenbelt.prism Σ₀ x₀ (O) (F.shape.o J I|>.K) (actual x) K
  have hi:= params_eq A.B.valid (m+1); have hψ:= params_eq A.B.valid m
  have hr': B'.hatBeta (m+1)=betaF G x₀ L:= PriceCompiler.beta_eq A.B.valid m
  have hb := A.B.support.cap N (m+1) hm
  have hb': B'.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G L x₀:= by
    have hh:= coverBill A.B.a (m+1)|>.2; refine hh.trans_eq ?_; change 2*B'.monitor (m+1)=2*Delay.fineMonitor G L _; unfold Calendar.monitor Delay.fineMonitor; rw [hr']; rfl
  have hg: (Σ₀).up.Bounds (Σ₀).high (X.p.profile J).width (X.p.profile J).paths (ConnectedActivityE6.loopBill G L x₀):= by rw [←hi]; exact {hb with two:=budget_loosen hb.two hb'}
  have hg' : (Σ₀).down.Bounds (Σ₀).low (X.p.profile I).width (X.p.profile I).paths (ConnectedActivityE6.loopBill G L x₀):= by
    have hh := A.B.support.cap N m hm.le; rw [← hψ]; exact {hh with two:=budget_loosen hh.two ((coverBill A.B.a m).2.trans (brace _ ht.1))}
  rw [show Local.Pure.script K Σ₀ X.O ρ β l k=Local.Pure.script K Σ₀ (F.target J I).table ρ β l k from congr_arg (fun X=>Local.Pure.script K Σ₀ X ρ β l k) (F.settles J I).symm]; exact ht.2 c _ S Σ₀ K X' V₁ V (B'.adm (m+1)) (Z'.laws.data.funds.patch rfl rfl) (show S.kernel=X.p.kernel from A.B.valid.kernel) he (congr_arg RG.Stage.clip hi) (congr_arg RG.Stage.clip hψ) hg hg' ρ hρ hK rfl l β (F.shape.c J I) r Z' rfl rfl hx.symm hx x rfl hr hB hx'

include hz
lemma palaces (k:ℕ) (i:Site c) : (V).Regular (neighbors d i) (chamber (strands u (steady Z' u k)) O k γ i) := Function.const _ (by
  let K:= Classical.choice (Tree.select (Pane.panel A m π).ratio (Pane.panel A m π).patch.odd_side)
  have he : ∀ i∈strands u (steady Z' u k), ∀ v∈Song.perf Z' i,Song.perf Z' i⊆ neighbors d v := by
    intro i hi v hv; apply (High.hall u _ u _ check_steady i ((runIn ..).1 hi) hv).trans; intro z' hz'; have hh:= (neighbors_mem ..).1 hz'; apply (neighbors_mem ..).2; exact hh.trans ((Nat.le_add_right ..).trans (traffic u _ B (V).B_pos))
  have hz' := weight A F π hm Z' hz K -- order?
  apply section_frame _ O (V) rfl he (perimeter ..) γ hz'.1 i
  ) H
end YM.AllOrder.Shop
