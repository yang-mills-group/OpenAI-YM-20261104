import YM.LocalLTE.Concert.Falls
/-!
# Price for Physical offers at arbitrary multiplicity. Stencil supplied real
traces scaled by the coupling (any power band). Every E anchor and forced K.
No inverse-price losses ignored.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side} (P:Rep G n) (B:BudgetPoint)
variable {V α :Type}[DecidableEq V] (R:Census V)
open FrameBox Grove Cabana
open AnalyticBridge VerifiedReset Collection
open Animals ConnectedActivityE6 Blaze Brush
-- true metadata before any compression. α mode need not singleton. scale can be location.R.
structure LoopBank (G:Gauge) (n:Side) (R:Census V)(α:Type) where
   origin : V→ Site n
   units : V→ ℂ
   select : α→ R.Mode
   walk : α → Walk
   scene : α→Site n
   tone: α→(G.Mat →L[ℝ] ℝ)
   phase:α→Bool
   scale: α→ℝ
variable (K:LoopBank G n R α)(b d:ℕ)(μ:ℝ)
namespace LoopBank
def wires (i:α):= (Animals.neighbors (b+1) (K.scene i))
def wall (i:α):= (Animals.neighbors b (K.scene i))
def realSignal(i:α): Config G n→ℝ:= traceT (K.scene i) (K.walk i) (K.tone i)
def signal(i:α): Config G n→ℂ:= Hue (K.scale i) (K.phase i) ∘ realSignal R K i
local notation "A₁"=> wall R K b
local notation "V₁"=> wires R K b
local notation "f₀"=>realSignal R K
local notation "f₁"=>signal R K
structure Legit (M Z:ℝ) : Prop where
   honest i: (K.select i).val.Nonempty
   traced i: (K.walk i).length ≤ b
   spends i: ‖K.scale i‖≤ Z
   traces i A: ‖K.tone i A‖≤ M*‖A‖
   closes i: Lattice.stop (K.scene i) (K.walk i)= K.scene i
   conjugacy i u v: K.tone i (G.mat (u*v*u⁻¹))=K.tone i (G.mat v)
   fruits i v : v∈(K.select i).val→ K.origin v∈ wires R K b i
   possible : 0 ≤ M ∧ 0 ≤ Z
-- gauges.Conjugacy. Mark mode repeated.T.Ch.H.
def baked : Layers P R α:=⟨K.origin,K.units,(K.wires R b), K.select, signal R K⟩
variable (A:(i:α)→Grove (K.scene i))
def modelRain (i:α):= Hall.shave (A i) b μ d (realSignal R K i)
def model (i:α):= Hue (K.scale i) (K.phase i) ∘ modelRain R K b d μ A i
local notation "H₀"=> baked P R K b
local notation "g₀"=> modelRain R K b d μ A
local notation "g₁"=> model R K b d μ A
variable {x a T J c d' z φ η:ℝ} (hk:Reliable G μ a)
-- event calendar possibly β argument.T.Funds.
variable (hX:Legit R K b J T) (hq:∀ i,P.p.supBounds (K.scene i) (wires R K b i) (realSignal R K i-modelRain R K b d μ A i) z)
local notation "C'"=> slotPay G J b P.p.order P.p.power
local notation "P'"=> P.p
abbrev sonic (b l j:ℕ):ℝ:= (1+(↑(b+1):ℝ))^(l*j)
lemma sunny (b l j:ℕ):0≤ sonic b l j:=by unfold sonic; positivity
local notation "C''"=> (sonic b P.p.power P.p.order)
abbrev payment (P:BudgetPoint)(α a:ℝ)(b:ℕ):= α* sonic b P.power P.order*a -- multiplication
local notation "U₀"=> payment P.p T
-- The following estimates use the payment U₀ fixed above.
include hX
omit hX in
lemma wired (i) : K.wall R b i⊆K.wires R b i:=fun _ hj=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans (Nat.le_add_right ..)) -- include hX unused remove
lemma glow(i:α): P.p.Regular (V₁ i) (f₀ i):=by
    apply VerifiedReset.reg_larger (traceDuty P.p _ _ b _ (hX.traced _) (hX.closes _) (hX.conjugacy _)) (wired R K b i)
lemma wins (i:α): P.p.supBounds (K.scene i) (V₁ i) (f₀ i) C' := by
    let D:=G.colorScale; refine ⟨mul_nonneg hX.possible.1 (by have hG:= G.colorScale_pos; positivity),fun U _ v hl hL=>?_⟩ -- `unfold ... at *` edit
    exact traceBound P.p U _ _ b _ (hX.traced _) (hX.traces i) hX.possible.1 v hl hL
lemma raysP : (H₀).Ready:= ⟨⟨hX.honest,hX.fruits⟩,fun i=> Port.hueReg _ _ _ (glow P R K b hX i) _ _⟩ -- order hW
lemma legalK(i:α)(U:Config G n): ‖Layers.residual (H₀) i U‖ ≤ T*C':= by
    unfold Layers.residual; split
    · rw [norm_zero]; exact mul_nonneg hX.possible.2 (wins P R K b hX i|>.1)
    change ‖Hue (K.scale i) _ _‖≤ _; rw [hueCost]; exact mul_le_mul (hX.spends _) (traceBound P.p U _ _ b _ (hX.traced _) (hX.traces i) hX.possible.1 [] (by simp) (by simp)) (norm_nonneg _) hX.possible.2 -- infer f_fix
lemma wind (i:α)(f:Config G n→ℝ)(y:ℝ)(h:P.p.supBounds (K.scene i) (V₁ i) f y)(hb: P.p.Regular (V₁ i) f)(v:V)(hv:v∈(K.select i).val): P.p.supBounds (K.origin v) (V₁ i) (Hue (K.scale i) (K.phase i) ∘ f) (payment P.p T y b):=by
   have hz:1+(separation (K.scene i) (K.origin v):ℝ) ≤ 1+(↑(b+1):ℝ):= add_le_add le_rfl (by exact_mod_cast ((neighbors_mem ..).1 (hX.fruits i v hv)))
   have hs:= Fan.spokeR P.p hz h
   have hy:= Port.hueRad f _ _ hb (K.scale i) (K.phase i) (K.origin v) hs
   -- VerifiedReset.sup_le maybe only real.; copy
   refine ⟨by unfold payment; exact mul_nonneg (mul_nonneg hX.possible.2 (sunny ..)) h.1,fun U h' l hl hd=>(hy.2 U h' l hl hd).trans ?_⟩
   unfold payment; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (hX.spends i) hs.1
include hk
omit hX in
lemma orbit(i:α): P.p.Regular (V₁ i) (g₀ i):= VerifiedReset.reg_larger (FrameBox.legal _ _ hk _ _) (wired R K b i)
lemma aroma (i:α): P.p.Regular (V₁ i) (g₁ i) ∧ P.p.Regular (V₁ i) (f₁ i-g₁ i):=by
   constructor; · exact Port.hueReg _ _ _ (orbit P R K b d μ A hk i) _ _
   rw [signal,model,hueDiff]; exact Port.hueReg _ _ _ (VerifiedReset.reg_sub (glow P R K b hX i) (orbit P R K b d μ A hk i)) _ _ -- order
include hq
set_option quotPrecheck false
lemma aromaPay (i:α)(v:V)(hv:v∈ (K.select i).val): P.p.supBounds (K.origin v) (V₁ i) (f₁ i-g₁ i) (payment (P.p) T z b) ∧ P.p.supBounds (K.origin v) (V₁ i) (g₁ i) (payment P.p T (C'+z) b) := by
     have hp:= orbit P R K b d μ A hk i; have h:= glow P R K b hX i; have ht:= hq i; constructor
     · unfold signal model; rw [hueDiff]; exact wind P R K b hX i _ _ ht (VerifiedReset.reg_sub h hp) v hv
     apply LoopBank.wind P R K b hX i _ _ _ hp _ hv
     let g:=(g₀ i); have he:g= f₀ i-(f₀ i-g):=by abel
     rw [show g₀ i=f₀ i-(f₀ i-g) from he]; exact VerifiedReset.sup_sub h (VerifiedReset.reg_sub h hp) (wins P R K b hX i) ht -- order
end LoopBank
end YM.LocalLTE.Port
