import YM.Qlocal.Gauges.Elfin
/-!
# Restoring at the physical mark and certificate prices.Piece supports & tag unaltered except alias.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges.Lamp
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload YM.Qlocal.Gauges.Atlas
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Planet Atlas Quipu Quipu.Sonnet
open RGComparison01 RGComparison01.Pledge Pressure
open ConnectedActivityE6 ConnectedActivityE6.Channel AnalyticBridge VerifiedReset Collection Quotes
open SliceRows Coat Baked Palette Resin Checks Song Refrain
open Next.Foundations Pressure.Stores Next.Fluctuations SectorMeasure Oriented Tree
open Planet Parabola Scribe Stowe
variable {Ω ι J V K κ : Type} {G:Gauge}{c f L:Side}
    {P: RG.Rep G f}{P': RG.Rep G c} [DecidableEq V][Fintype V]{R:Marker.Census V}
    {o:V→Site f}{s:V→Support f}{q:R.Mode→ℝ}
    {p:BudgetPoint}{A A' δ τ w r κ₀ v q' a b:ℝ}
    {S:StepData c f}{Z₀:Teller G}{Q:ConnectedActivityE6.Target G Z₀}{T: Tube G S}
    {W β μ C₀:ℝ}{O: Target.Order G W} {j k m ℓ N d:ℕ}
variable (U:Cash W β μ L Q O C₀ T P) (X:Lamp R Ω P o) (χ:Chi)
variable {x:Ω} {Y:Taste Ω o P R}{dcl:Set (ℕ ×ℕ)}
    {h₁:RetainsDeclared dcl Y s} {h₀:Peak P o Y q P.p.supportExponent δ δ}
    (hp:Payload.Fabric h₁ h₀ x)(F:Ω→ Senses R→ℂ)(L': HasSlots P.p P.activities)
variable (J':Ribbon P j)
set_option quotPrecheck false
local notation "f₀"=> Atlas.intoK R s o X.census
local notation "Lℓ"=> Drawing.cabinet U J'
local notation "Dk"=> Payload.deck R s
local notation "K₁"=> Notice R
local notation "G!"=> X.roster_ hp F L'
local notation "S!"=> Atlas.Stakeup R o s X.census
local notation "Φ"=> Atlas.Loft R s
local notation "Ψ"=> Planet.Whole (Atlas.Loft R s)
local notation "τ'"=> tag R s
local notation "Y₀"=> (fun i:S!=> (G! x i).M)
local notation "Y₁"=> (fun j:Ω=>fun i:S!=> (G! j i).M)
local notation "Za"=> X.roster hp F L'
namespace Frame
variable (I:Frame R Ω G S) (hX:PledgeAt U X χ J' I ℓ m p s a b)
variable (p':Rental q)(hf:∀ x i,q (i:Senses R).val* ‖F x i‖ ≤1)(hz:0<δ)(hd:δ≤1)(hv:1≤v)
local notation "s₀"=> (Revenue.compile q v δ s (o:=o) (k:=X.census))
local notation "μ'"=> Revenue.shift q v δ F s
local notation "Xo"=> Span.specification S.ratio s
local notation "dβ"=> (Translation.scribe (Atlas.slate R s) μ')
noncomputable def notice_top (I:Frame R Ω G S) (f:Ω→ Senses R→ℂ) : Scribe Ω (Notice R) G c R where
 tag:=Atlas.grade R
 total:=fun _=>False
 region:=I.holder
 score x p Vw:= (∏ j∈p.val, f x j) * ↑(I.view x p Vw)
local notation "N!"=> Fintype.card V
include hv
lemma term_restore (i:Notice R)(x:Ω) : ↑(phCurrency i v) *Translation.falls (slate R s) (μ' x) ((tag R s) i) = (∏ j∈ i.val,F x j):= by
 unfold Translation.falls; rw [if_pos (excellent i)]; unfold phCurrency; push_cast; rw [show (∏ i'∈(tag R s i).val,(μ' x i'))=∏ j∈i.val,(μ') x (Sum.inr j) from Finset.prod_map ..]
 -- type coe ℂ: casting annotation.Boom. 
 have ht : (∏ _∈ i.val,(v:ℂ)⁻¹)=_:= (Finset.prod_const (b:=(v:ℂ)⁻¹) (s:=i.val)); rw [← ht,← prod_mul_distrib]; refine Finset.prod_congr rfl fun j _=>?_; unfold Revenue.shift; change (v:ℂ)⁻¹*(F x j/↑(v⁻¹))=_; field_simp [(Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hv).ne')]; push_cast; field_simp [(Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hv).ne')]
lemma identity_ready : Translation.scribe (Atlas.slate R s) (Revenue.shift q v δ F s) (ready I s v) = notice_top I F:=by
 unfold Translation.scribe ready publish notice_top; simp only [Atlas.sieve]; congr 1; funext i j y; change Translation.falls (Atlas.slate R s) (μ' i) ((tag R s) j) * (↑(phCurrency j v*I.view i j y):ℂ)=_; rw [Complex.ofReal_mul,mul_left_comm, ← mul_assoc (↑(phCurrency j v):ℂ), term_restore F hv] -- check arguments
include hp p' hf hz hd hX L'
-- The remaining rows have at least one old nonmodel mark. Their rough costs are retained.
local notation "Hκ"=> genuine U X χ hp F L' J' I a b hX
local notation "R'"=> Palace.Counter.remaining U Za s₀ χ f₀ J' m (loom R s I) (Atlas.tag_unique R s) Hκ
lemma hCheck (hu: Proper R' p Xo) : Translation.Check (slate R s) (Revenue.shift q v δ F s) R' (Palace.blank Φ) q (δ*v^N!) := by
 intro x i ht; apply le_trans (b:=δ*v^N!) ?_ (by show _ ≤ _ * 1; rw [mul_one]);
 let V:= (R') ; apply Revenue.entrance p' F hz hd hv hf _ x; rotate_left; 
 · intro hq; apply ht; unfold Palace.Counter.remaining eligible;  dsimp only; rw [if_neg (by exact not_not.mpr hq)]
 exact regular_ray_nonempty_ _ (fun h=>ht (hu.quiet _ h _))
end Frame
end YM.Qlocal.Gauges.Lamp
