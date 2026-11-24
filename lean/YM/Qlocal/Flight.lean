import YM.Qlocal.Caption
import YM.Qlocal.CoverLease
/-!
# Uniform through one genuine reclosure at fixed currency

This solver before restore of chosen booking.Shape terms. Every startup
address (fine support & mask) reaches a genuine root-dependent set on the next
carrier. `τ` only consumed to loosen the root reserve. Need schedule ballots
 for choosing `KLink` & final lease, stability etc; these functions combine
 the real normalization and launch estimates. This is the multipart real-part
 of the later supplier; does NOT bound the Fk comparison yet. Applies to every
 counted row of the input (any mixed-degree incl arbitrary old forced within
this budget). Many derivatives at tested norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Flight
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Pressure Pressure.Stores Next.Fluctuations SectorMeasure Oriented Tree
open ConnectedActivityE6 ConnectedActivityE6.Channel AnalyticBridge VerifiedReset Collection Quotes
open SliceRows Coat Baked Palette Resin Checks Song Refrain

variable {Ω ι J V : Type} [DecidableEq V] {R:Marker.Census V} {G:Gauge}{c f L:Side}
    {P: RG.Rep G f}{P': RG.Rep G c}
    {X:Support f}{o:V→Site f}{s:V→Support f}
    {u w:V→ℝ}{z z':R.Mode→ℝ}{k k' : ℕ}{a b d δ Dℓ ε C A B θ ρ e v t w₀:ℝ}
    {S:StepData c f}{Z₀:Teller G}{Q: ConnectedActivityE6.Target G Z₀}{T: Tube G S}
    {W β μ C₀:ℝ}{O: Target.Order G W}
    {Δ:ℕ→Prop}{D':Set (ℕ ×ℕ)}

variable (U:Cash W β μ L Q O C₀ T P)
local notation "S0"=> (fun i=> S.ratio.parent (o i))
local notation "Z1" => fly S.ratio ∘ s
variable {M:ι→Leaf P}{D: Ω→ι→Leaf P}

set_option quotPrecheck false
local notation "Ψ" => U.supportP ∘ Palette.sign M S
lemma inherits (Y : ι→Poly R) (h: Syntax Y s (fun i=> (M i).crest)) : Syntax Y (fly S.ratio ∘ s) (U.supportP ∘ Palette.sign M S):=
   ⟨h.proper,(fun i q ht j hj=> Finset.Subset.trans (Finset.image_subset_image ((h.mental i) q ht j hj)) (Stowe.enrolled M U i)),h.repeated⟩
lemma narrows {X:Spectrum Ω ι G c J}{L:ι→Support c} {Z:BudgetPoint} (h:X.Costs Z L a A)(he:d ≤ a): X.Costs Z L d A:= by
 obtain ⟨x,hf,hQ⟩:= h.rent.majorize; refine {h with rent:=⟨x,hf,fun i=>budget_mono (hQ i) (fun i=>?_) (fun i=>?_)⟩}; · split; exact mul_nonneg (hf _|>.1) (Real.exp_nonneg _); rfl
 split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (hf _|>.1); rfl

variable (r:Roster M D) (p:P.p.threshold>0) -- P.p is input ; never compare threshold, no need
    (α:ℝ) (g:ι→ℝ) (χ:Chi) (D₀: Match.Alliance U U 1 0)
local notation "p0" => P'.p
local notation "s★"=> (P'.p).supportExponent
local notation "D★"=> (Beam.marquee U p0).read (plusone U D₀ χ α)
local notation "K★"=> fun x=> shoot (D x) U χ g U D₀
local notation "F★"=> P'.activities
local notation "D!"=> KLink p0 D★ v d p0 F★ w₀ s★

variable [Fintype ι] (Hr:Primitive.Earnings U χ r α P'.p g D₀ Δ k e v δ t A a)
-- Earnings fully qualify. gτ.Z unmasked. step from CoverLease.Name.
    (R₁: KLink P'.p ((Beam.marquee U P'.p).read (plusone U D₀ χ α)) v d P'.p P'.activities w₀ P'.p.supportExponent)
local notation "λ!"=> Primitive.table U χ r g
local notation "Lℓ"=> (fun x i=> Ink.yielded (D x) g U (χ:=χ) (r.castLabel U x i))
local notation "Wℓ"=> (R₁.carry K★)
variable (M':ι→Poly R) (Y : Taste Ω o P R)
    (hn: Syntax M' s (fun i=>(M i).crest)) (ht:∀ i:V,o i∈s i)
    (he : Peak P o Y z P.p.supportExponent B C)
    (hv:P'.eval=S.push P.beta P.eval)(hp: ∀ i,P'.eval i≠0) (hT:P'.p.threshold=Pressure.temp β) {F0:Config G c→ℝ}
    (hS : SwitchStep (J:=Cl M U) D S g F0 ((Beam.marquee U P'.p).read (plusone U D₀ χ α)) P'.p (fun x=> shoot (D x) U χ g U D₀) (fun (x:Ω) (i:Baked.Cl M U)=> Ink.yielded (D x) g U (χ:=χ) (r.castLabel U x i)))
    (hz: d ≤ a)(hπ:P'.p.supportExponent ≤ a) -- true
open Publishing
set_option quotPrecheck false
local notation "Gκ"=> Publishing.script M' Wℓ λ!
-- `λ!` may invalid
local notation "Yκ"=> (Gκ).taste P' (S.ratio.parent ∘ o) (fly S.ratio ∘ s)

variable [Fintype V] [Nonempty V]
variable (hw : RetainsDeclared D' Y s) (hi: Brand M' z' Dℓ)(hR: ∀ i,0<z i)(hu: ∀ i,0<z' i)
    (hy : P.p.B ≤ 2*P'.p.B) (hα: P'.p.supportExponent*Footprint.conversion S.ratio 0 ≤ P.p.supportExponent)
    (hu':0≤ε) (hε:∀ i:R.Mode,i.val.Nonempty→ z' i ≤ ε*z i)
    (hP:∀ x, (Photo.given (S:=S) (D x) g R M')=(Y.leaf x).contents.density)
section boarding
include U hi ht he hR hu hw hy hα hu' hε hP
variable [Countable J] [Nonempty Ω] {K : WayK Ω ι G c}{L₀ : Ω→ J→ Config G c→Ways ι}
    (hf:SwitchStep D S g (Real.exp ∘ P'.exponent) P'.activities P'.p K L₀)
variable (L' : Spectrum Ω ι G c J) (hw':L'.Reads P'.p L₀) {Γ: ι→ Support c} (hQ': Syntax M' (fly S.ratio ∘ s) Γ) (ht' : L'.Costs P'.p Γ P'.p.supportExponent A)(hh:UniformPays P'.activities P'.p K w₀ P'.p.supportExponent)
    (hg:∀ x i (y:Site c), y∈Γ i→ Merge.Motion.Hush i y (fun i=> (P'.activities.forced i).support) (K x)) (f₀:J→ℝ) (hb:Summable f₀)
    (hf₀ : ∀ x i,Paid (fun U=> L₀ x i U) (f₀ i))
set_option quotPrecheck false
local notation "Sκ" => (Publishing.script M' K L').taste P' (S.ratio.parent ∘ o) (fly S.ratio ∘ s)
include hf hw' hQ' ht' hh hg hb hf₀
lemma boarding : Peak P' (S.ratio.parent ∘ o) (stay S Y Sκ) z' P'.p.supportExponent
     (Dℓ*A+ cost S P'.p.supportExponent*(ε*B)) (Dℓ*w₀)∧
     RetainsDeclared (Declared P' (fly S.ratio ∘ s) R) (stay S Y Sκ) (fly S.ratio ∘ s)∧
     ∀ x,S.push P.beta (Y.leaf x).density= ((stay S Y Sκ).leaf x).density := by
  let e : ∀ i:V,(S.ratio.parent ∘ o) i∈(fly S.ratio ∘ s) i:=fun i=> Finset.mem_image_of_mem S.ratio.parent (ht i)
  have hx0:= weighs P' hQ' e L' hw' ht' hh hg
  have h₁: RetainsDeclared (Declared P' (fly S.ratio ∘ s) R) (Sκ) (fly S.ratio ∘ s):= Publishing.retains_ hx0;
  have hx:= Publishing.assemble hx0 z' (fun i=> (hu i).le) (levels P' hQ' e L' hw' ht' hh hg (fun i=>(hu i).le) hi rfl); have hs:=P'.p.exponent_pos
  refine ⟨ (StageArt.earned (ρ:=ε) S he hx hy hα hs.le hu hu' hε), StageArt.retained S hw h₁, fun x=>?_⟩
  funext V; rw [StageArt.incumbent S he hx P.p.exponent_pos.le hs.le hR hu x V,show (Y.leaf x).density= (fun v=> Poly.pass (Y.leaf x).captions.chord * (Photo.given (S:=S) (D x) g R M') v) from (by rw [hP x]; exact funext (StageArt.detached P.p.exponent_pos.le he x hR))];
  have hY: S.IsKernel P.beta G:= S.isKernel (funds_branch U.laws.intake.ready) _;
  have hp : Integrable (Photo.given (S:=S) (D x) g R M') (prior G f):=by unfold Photo.given; refine integrable_finsetSum _ fun i _=>?_ ; exact ((((Palette.team _ i).sells U.laws.intake.cap).1.integrable _).mul_const _).smul_const _
  rw [MergeProof.Menu.convective (Y:=Photo.given (S:=S) (D x) g R M') _ _ _ hY hp]
  exact congr_arg (_*·) (Service.answers hQ' e L' hw' ht' hh hg U hf le_rfl f₀ hb hf₀ x V)
end boarding
include U hp R₁ Hr hi hn ht hv he hπ hz hT hS hR hu hw hy hα hu' hε hP
set_option maxHeartbeats 400000 in
/-- This exposes exact mask reclosure and peak. Can license with ζ-specific precision. -/
theorem flying [Nonempty Ω]: Peak P' (S.ratio.parent ∘ o) (stay S Y Yκ) z' P'.p.supportExponent
     (Dℓ*A+ cost S P'.p.supportExponent*(ε*B)) (Dℓ*w₀)∧
     RetainsDeclared (Declared P' (fly S.ratio ∘ s) R) (stay S Y Yκ) (fly S.ratio ∘ s)∧
     ∀ x,S.push P.beta (Y.leaf x).density= ((stay S Y Yκ).leaf x).density := by
 obtain ⟨f0,hb,hf0⟩:= Primitive.payment U χ r α P'.p g D₀ Hr hT (P'.p.exponent_pos.le.trans hπ)
 have hF := Hr.force.relax (le_refl v) hz
 let Γ:= U.supportP ∘ Palette.sign M S; have hg x i (y:Site c) (hp:y∈Γ i): Merge.Motion.Hush i y (fun i=> (P'.activities.forced i).support) ((R₁.carry K★) x):= R₁.addresses _ _ _ (Hr.force_addresses _ _ _ hp)
 exact boarding U g M' Y ht he hw hi hR hu hy hα hu' hε hP (SwitchStep.finish_into hS hF R₁ hv hp) λ! (Primitive.reads U χ r α P'.p g D₀ Hr) (inherits U M' hn) (narrows (Primitive.rental U χ r α P'.p g D₀ Hr) hπ) (R₁.rolled hF) hg f0 hb hf0
end YM.Qlocal.Flight
