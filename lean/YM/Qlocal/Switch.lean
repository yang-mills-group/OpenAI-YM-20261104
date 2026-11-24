import YM.Qlocal.Forced
import YM.RGComparison01.Marks.TokenRoots

/-!
Full *switch statements* before any normalization, quotient, specialization
or marker extraction. These retain vacuum (and actual orientation parameters).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ₀ : Chi}


open Function Filter Lattice RG RG.Patch Pressure Ovens
open Mallow Motion Progress.DirectedRecipe Refrain Song
open Palette Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas Switch

variable {J : Type} [Fintype ι] (M : ι→Lotus.Leaf R) (D : Ω→ι→Lotus.Leaf R)

-- λ ∈ [0,1] with idempotent-like tags, lift nilpotent tags via native `Switch.jet`.
-- NB t=1 not evaluation of the square-zero algebra as real numbers; this is
-- just one analytic precursor. All disjoint lists recovered at projection.
lemma buy_back (S:StepData c f) (g : ι→ℝ) (t:Finset ι) :
    Palette.buy M (Palette.ways g 0 t) S=R.eval := by
  ext U
  let p : Tickets (Palette.sign M S) := Tickets.none _
  unfold Palette.buy; rw [sum_eq_single p]; rotate_left
  · intro i hi ht; have he : i.val.Nonempty:= nonempty_iff_ne_empty.mpr (fun hl=> ht (Subtype.ext hl)); unfold Palette.sale; rw [amplitudes,click]; split; · rw [zero_pow (by exact (card_pos.mpr he).ne'),zero_mul,zero_mul]
    rw [zero_mul]
  · simp
  change ((∏ _∈(∅:Finset ι), _) * _) = _
  rw [prod_empty,one_mul]
  let m:=Palette.team M p; have hx:m.own=∅:=image_empty M
  have ht : m.gasDue=∅:= eq_empty_iff_forall_notMem.mpr (fun i=>by rw [Team.asked,hx]; simp)
  have hh k : m.bun k U=R.activities.gasOccurrence R.p k U:=by
    unfold Team.bun Team.bill Activities.gasOccurrence
    split; · rw [ht,if_pos (empty_subset _),sdiff_empty,ingredients,hx,prod_empty,one_mul]
    rfl
  change Real.exp _ * ∑' k,m.bun k U=_
  simp_rw [hh]; rfl

/-- Uses the actual beta of this step, not an executable formal one. `A`
 may be an early output table prior to reset. At exit must bind `F`.
 The whole switching equation precedes specializing to nilpotent z or dividing. -/
structure SwitchStep (S:StepData c f) (g:ι→ℝ) (F:Config G c→ℝ)
    (A:Activities G c) (p:BudgetPoint) (K: WayK Ω ι G c)
    (L:Ω → J → Config G c → Ways ι) : Prop where
  all x (U:Config G c) t (ht:t∈Set.Icc (0:ℝ) 1) (s:Finset ι) :
     S.push R.beta (buy (D x) (Palette.ways g t s) S) U=
       F U * Real.exp (∑' i,L x i U t s) * (black A (K x t s)).gas p U
  baseL x i V s : L x i V 0 s=0
  baseK x s : K x 0 s=A.K

namespace SwitchStep
variable {A:Activities G c} {p:BudgetPoint} {F:Config G c→ℝ} {K: WayK Ω ι G c}
    {𝕃:Ω → J → Config G c → Ways ι}
    {g:ι→ℝ} {D} (h: SwitchStep D S g F A p K 𝕃)
include h
lemma unmarked (x:Ω) U : S.push R.beta R.eval U = F U * A.gas p U:= by
    have hv:= h.all x U 0 ⟨le_rfl,zero_le_one⟩ ∅
    rw [buy_back, show (black A (K x 0 ∅)).gas p U=A.gas p U from (by rw [h.baseK]; rfl)] at hv
    simpa only [h.baseL,tsum_zero, Real.exp_zero,mul_one] using hv
-- beware dependence binder Ω empty; claim x only
open Marker
variable (Y:Cash W β μ L Q o C T R) -- Q/o may not needed except Response.phoenix
include Y
lemma full (W0:UniformPays A p K b a) (hr:p.supportExponent≤a)
    {α:Type} [DecidableEq α] [Fintype α] (C:Census α)(z:ι→Poly C)
    (hz:∀ i,z i*z i=0)(hZ:∀ i,(z i).part C.quiet=0)(U: Config G c)
    (f:J→ℝ) (hf:∀ x i, Paid (fun _: Unit => 𝕃 x i U) (f i))(hs:Summable f)
    (x:Ω) :
    S.push R.beta (Photo.given (S:=S) (D x) g C z) U=
     (F U:ℂ) • (Poly.pass (∑' s,sound z (𝕃 x s U))*∑' i,Photo.fronts A (fun i=>sound z (fun t s=> K x t s i U)) U p i) := by
    exact Response.phoenix (H:=Y) (D x) g U (F U) A p (K x) (fun j=> 𝕃 x j U) C z hz hZ (fun i=> h.baseL x i U) (Story.downsized p (W0.project x) hr) (fun t ht T=>(h.all x U t ht T).symm) (hf x) hs
end SwitchStep

namespace Roster
variable {M D} (h:Roster M D) (p : BudgetPoint) (g:ι→ℝ) (I: Cash W β μ L Q o C T R) (χ: Chi)
include h
local notation "castI" => h.castLabel I
omit [Fintype ι] in
lemma retag (x:Ω) (he:UniformRooted (origins M I) (entry I h g χ) p a e) :
    Checks.Rooted (origins (D x) I) (fun s => glass (D x) g χ s) p a e:= by
   obtain ⟨f,hf,hv⟩:= he.specializes x
   -- 
   refine ⟨fun i=>f ((h.castLabel I x).symm i),fun i=>?_,fun i=>?_⟩
   · obtain ⟨j,rfl⟩:= (h.castLabel I x).surjective i; dsimp only; rw [Equiv.symm_apply_apply, h.geometry]; exact hf j
   convert budget_pull (castLabel I h x).symm (castLabel I h x).symm.injective (hv i) using 1; ext j; have hd:(origins M I ((h.castLabel I x).symm j)) = origins (D x) I j:= by rw [← h.geometry I x, Equiv.apply_symm_apply]
   dsimp only; rw [hd]
end Roster

namespace Primitive
open Ink
variable (Y:Cash W β μ L Q o C T R) (χ:Chi)
variable {M D} (h:Roster M D) (γ:ℝ) (p:BudgetPoint)
    (g:ι→ℝ) (F:Forest S.ratio) (D':Match.Alliance Y Y 1 0)
set_option quotPrecheck false
local notation "ℬ"=> Beam.marquee Y p
local notation "𝔸"=> (Beam.marquee Y p).read (plusone Y D' χ γ)
local notation "Sᵥ"=> Y.supportP
local notation "K₀"=> fun x=> shoot (D x) Y χ g Y D'
local notation "Xᵥ"=> Story.amplitude ℬ p (plusone Y D' χ γ) R.beta γ (weighty Y χ F) T.down T.low
local notation "L₀" => (fun x i=> Ink.yielded (D x) g Y (χ:=χ) (h.castLabel Y x i))
-- `Roster.base` unused includes.
variable {u g₀ h₀ s₀ v₀:ℝ→ℝ}{k k' p' :ℕ}{ν:ℝ}
variable (hQ: Cellar Q χ W L S.patch o p.order k k' p.power μ a δ v₀ g₀ h₀ s₀ u β)

/- This intermediate result will be preserved in the final construction. All weights
   such as g here are in the LOCAL RENTAL convention (`v₀ β`, which can
   require rescaling payloads as described in the manuscript's proof).
   Layout geometry for root `k` is carried by `recordSet` of the Cl; `originHush`
   is on the whole forced branch. Retiring cut refers to fixed M Cl here; equivalent
   via the relabelling above. Unmasked E-log fields from input? via actual H Cash.
-/
structure Earnings (S₁: ℕ→Prop) (k' : ℕ) (z v e y s : ℝ) (a : ℝ) : Prop where
  force : UniformPays (𝔸) p (fun x=> shoot (D x) Y χ g Y D') v a
  masking x i : Pillow.pottery (D x) g χ (h.castLabel Y x i) = masked p.threshold (origins M Y i) (entry Y h g χ x i)
  force_addresses x j w (hp:w∈ Y.supportP (Palette.sign M S j)) : Motion.Hush j w (fun i=> ((𝔸).forced i).support) (shoot (D x) Y χ g Y D')
  log_all : UniformRooted (origins M Y) (entry Y h g χ) p a s
  log_retire : UniformRooted (origins M Y) (crop Y h g (fun z : Cl M Y=> Season.Heavy k' z ∧ ¬Season.Ode S₁ z) χ) p a z
  log_inherited : UniformRooted (origins M Y) (crop Y h g (Season.Ode S₁) χ) p a (y*e)

variable (hh: p.threshold= Pressure.temp β)(hB:p.B=radiusB β)
    (hs : Pledge.Bench M g (v₀ β))(hX: Stamp T)
variable {Ψ:ℕ→Prop} (hF : (Tithe.portion R.activities Ψ).EBound R.p e)
    (hFe : e ≤ incomingE G L β) (hw : Height.grow G L β^k ≤ Real.exp (Q.mark L μ β))
set_option quotPrecheck false
local notation "ℌ"=> Earnings Y χ h γ p g D'
local notation "𝒱"=> Real.exp (-Q.mark L μ β) * (2*(16*g₀ β))
local notation "𝒲"=> h₀ β / (Height.grow G L β^k)
include h hh hB hQ hs hX hF hFe hw

theorem earned : ℌ Ψ k' 𝒲 𝒱 e (s₀ β) (h₀ β) a := by
  obtain ⟨hm, hr,he,hv⟩:= uniform_retirement Y h p g hh hB hQ hs hX hF hFe hw
  have hR:= (hQ.buys c f S T rfl hX R C Y).1
  refine ⟨MarkExit.wages M D Y χ h g p hh hB γ D' (hR _ M g hs) (fun x=>hR _ _ _ (h.bench x hs)),hm,fun x j w hp=>?_,hr,he,hv⟩ -- argument h.bench?
  rw [← h.marks x] at hp; exact Stripes.originHush (D x) g Y p j w hp D'

variable {z xι q' ξ θ Λ ε t A d₁ d₂ d₃ σ N₀:ℝ} (P1:Captain Y j xι d₁ d₂ t A q' r b ν p' χ)
    (hT:T.down.Bounds T.low σ θ Λ) (ht:p.order ≤ j)(hZ: Cash.Renewed n z d₃ ε Y)

include P1 hT ht hZ

/-- The priced regular and forced arrays are attached to one *actual* full
 output, retaining any fixed vacuum error `e` supplying the local hit.
 This statement can be used before final scalar/coupling reset/repackaging. -/
theorem complete : SwitchStep D S g (Xᵥ) (𝔸) p K₀ L₀ ∧
     ℌ Ψ k' 𝒲 𝒱 e (s₀ β) (h₀ β) a := by
  let hK:= earned Y χ h γ p g D' hQ hh hB hs hX hF hFe hw
  refine ⟨⟨fun x V t hv T=> ?_, fun x i V s=> Ink.blanker .., hK.force.term⟩,hK⟩
  have hR := (hQ.buys c f S _ rfl hX R C Y).1 ι (D x) g (h.bench x hs)
  let f (i:Cl (D x) Y):= Ink.yielded (D x) g Y (χ:=χ) i V t T
  have he : ∑' i, f (h.castLabel Y x i)= Heron.bouquet (D x) g Y V t T (χ:=χ) := Equiv.tsum_eq (h.castLabel Y x) _
  change _= _*Real.exp (∑' i,f (h.castLabel Y x i)) * _; rw [he]; apply Eq.symm
  apply Story.arcs _ _ Y D' p γ hh.symm hB hR V F (h.retag p g Y χ x hK.log_all) ?_ P1 hT ht hZ t hv T
  intro z; obtain ⟨i,rfl⟩:= (h.castLabel Y x).surjective z; exact hK.masking x i

end Primitive
end YM.Qlocal
