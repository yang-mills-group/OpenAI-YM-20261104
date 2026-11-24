import YM.FVA2.MirrorRent
/-!
# No mere promise that a chosen seam has any agreed geometry and Hessians

Prove the actual paired step intertwiner on all full fields on both sides, including Schur and
image rule.Mirrored inputs.N.Schedules existential below (later). We couldn't replace `Λ.t`
by sign on projected stencil alone.Stating in real frames (same Gauge.Color.Roll.Ph. DC).
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
section common
namespace Mirror.Related
variable {E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]
variable (X:Mirror.House E F)(W:Quadratic E)(U:Quadratic F)
theorem from_square (h:∀x,W.flourish ( X.t x )=W.flourish x)(he:∀ x,W.flourish ( X.ε x )=2*U.flourish x): Related X W U:= by
     constructor
     · intro x y; have hx:= h (x+y); rw [map_add, Quadratic.biplus,Quadratic.biplus,h,h] at hx; linarith
     intro x y; obtain hx:= he (x+y); rw [map_add, Quadratic.biplus,Quadratic.biplus,he,he] at hx; linarith

lemma charged (w:PowerSeries ℝ)(f:E→ℝ)(g:F→ℝ)(hf: ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0)(h:f ∘ X.ε=ᶠ[𝓝 0] (2:ℝ) • g)(he:f ∘ X.t =ᶠ[𝓝 0] f): Related X (Quadratic.genesis w f) (Quadratic.genesis w g) := by
     refine from_square _ _ _ (fun x=>?_ ) (fun x=>?_ );
     · rw [Quadratic.native,Quadratic.native]; obtain hx := GermLaplace.jet_pull (LinearMap.toContinuousLinearMap X.t) f (hf.of_le le_top) x 2; rw [ show jet (f ∘ (LinearMap.toContinuousLinearMap X.t))=_ from (show jet (f ∘ X.t)=jet f from GermLaplace.equal_jet he) ] at hx; rw [ ← show jet f 2 x=jet f 2 ( X.t x ) from hx ]
     obtain hp := GermLaplace.jet_pull X.ε.toContinuousLinearMap f (hf.of_le le_top) x 2; rw [ show jet (f ∘ X.ε.toContinuousLinearMap)=jet ((2:ℝ) • g) from GermLaplace.equal_jet h, Inherit.times _ (2:ℝ) hg x ] at hp; rw [Quadratic.native, Quadratic.native, show jet f 2 (X.ε x)= _ from hp.symm]; ring
end Mirror.Related
end common
namespace Both
open Rent
variable {G:Gauge} {c f n:Side} (he:Even f.val)
local notation "H"=> Both.orb G f he
local notation "v0"=> (show Descent.Room G ( Descent.nil (top:=f)) from trivial)

theorem commencement (t:(Descent.nil (top:=f)).Tags) : Mirror.Related ( Both.orb G f he ) (retained ( Descent.nil (top:=f)) t v0 ) (OpenSlots.initialFull G f 1).Q:= by
     let W:= bareF G f; let R:= OpenSlots.firstBill (G:=G) (n:=f); let A:= Quadratic.genesis 1 W
     have hx:(retained ( Descent.nil (top:=f) ) t v0)=A:= by
          apply only_P; apply Quadratic.records; intro x; let B:=(retained ( Descent.nil (top:=f)) t v0); change B.flourish x= _; unfold A; rw [Quadratic.native,show term 1 0=(1:ℝ) from PowerSeries.coeff_zero_one,one_mul]; unfold W; rw [← CityHistory.frozen (x:=x) t ]; change B.flourish x= 2*(B.flourish x/2); ring
     rw [hx]; exact Related.charged ( H ) 1 W R (Legacy.born_hot ..) OpenSlots.firstGranted ( Filter.Eventually.of_forall (fun x=> Rent.top_bridge x) ) ( Filter.Eventually.of_forall (fun x=> Rent.top_flip ..) ) -- binder order

variable (S:StepData c f)(h:S.patch.Branches S.kernel G) (hc:Even c.val)(b:S.Choices)
local notation "T"=> Forestry S
local notation "P"=> canopy S
local notation "K"=> Both.orb G c hc
local notation "Y"=> Both.lights G S he
local notation "Z"=> Mirror.House.join Y K
local notation "L"=> Pins G f
local notation "O"=> Flats G f
local notation "C"=> Unmasked G f
local notation "M"=> Future G S T
local notation "Eo"=> Cross (G:=G) S P
local notation "lo"=> Flats G c
local notation "ξ"=> gate G S T
local notation "p"=> canopy S
-- R antecedent proof from seam alignment.
variable (A:Quadratic ( Pins G f ))(U:Unmasked G f)(r:Mirror.Related (Both.orb G f he) A U.Q)
variable (w:PowerSeries ℝ)(hw:PowerSeries.constantCoeff w=1)
local notation "Ψ"=> gateQ S T b A
local notation "Ω"=> gated P U b w

include h hw
lemma tax_pair : Mirror.Related (Z) ( Quadratic.genesis 1 ( tax S T b (G:=G) )) ( Quadratic.genesis w (substep P b)):= by
    have he₀ : Quadratic.genesis w (tax S T b (G:=G))= Quadratic.genesis 1 (tax S T b (G:=G)):= by apply only_P; apply Quadratic.records; intro x; rw [Quadratic.native,Quadratic.native, show term w 0=1 from (PowerSeries.coeff_zero_eq_constantCoeff_apply w) |>.trans hw, show term 1 0=(1:ℝ) from PowerSeries.coeff_zero_one]
    -- he binder shadow.local notation anticipates!
    rw [ ← he₀ ]; apply Related.charged; exact CityHistory.tax_hot S T b h; exact OpenSlots.subReady P b h; exact tollage S h he hc b; exact symmA S h he hc b
include r
lemma together_r : Mirror.Related (Z) Ψ Ω:= by
    obtain ⟨hT,hM⟩:= tax_pair he S h hc b w hw;
    constructor
    · rintro ⟨i,y⟩ ⟨j,x⟩; change A.P (pext G S T (atRef G S i)) (pext G S T (atRef G S j))+(Quadratic.genesis 1 ( tax S T b ) ).P _ _= A.P (pext G S T i) (pext G S T j)+_; obtain hv:= congr_arg (A.P (pext G S T i) (pext G S T j)+·) ( hT (i,y) (j,x) ); refine Eq.trans ?_ hv; congr 1; rw [ ← Both.full_reflect S i, ← Both.full_reflect S j ]; exact r.living _ _
    rintro ⟨x,i⟩ ⟨y,j⟩; change A.P (ξ ((Z).ε _)) (ξ ((Z).ε _))+(Quadratic.genesis 1 ( tax S T b (G:=G) )).P _ _=2*(U.Q.P (OpenSlots.extend P x) (OpenSlots.extend P y)+_); rw [hM,gate_ε S ..,gate_ε S .., mul_add ]; apply congr_arg₂ ( ·+· ) ( r.weight _ _ ) rfl

variable (hp: ( Quadratic.core (gateQ S ( Forestry S ) b A) ).RespectsPrice )(gi: (Quadratic.core (gated (canopy S) U b w)).RespectsPrice)
include hp gi
lemma cap_next : Mirror.Related K (Quadratic.reduced Ψ hp) (Quadratic.reduced Ω gi):= Related.earth Y K Ψ Ω (together_r he S h hc b A U r w hw) hp gi
-- Grass trick for dual.Y.Parameter.
local notation "Q₀"=> Quadratic.RespectsPrice.inner hp
local notation "Q1"=>Quadratic.RespectsPrice.inner gi
lemma frameMean (x:lo): (Y).ε (Quadratic.skew Ω gi x)= Quadratic.skew Ψ hp ((K).ε x):= ( Related.η_mean Y K Ψ Ω (together_r he S h hc b A U r w hw) hp gi x ).symm
include hc
lemma WickRule (ℓ m: Module.Dual ℝ (Future G S T)):
    (Q1).wick (ℓ∘ₗ (Y).ε) (m∘ₗ (Y).ε)= (Q₀).wick ℓ m + (Q₀).wick ℓ (m∘ₗ (Y).t):= by
    apply Mirror.images_wick; obtain hQ:= Mirror.Related.held Y K Ψ Ω ( together_r he S h hc b A U r w hw );
    rw [ ← show Quadratic.core ( gated P U b w )= Quadratic.recordQ (Q1) from only_P _ _ gi.choose_spec, ← show Quadratic.core (Ψ)= _ from only_P _ (Quadratic.recordQ Q₀) hp.choose_spec ]; exact hQ
end Both
end YM.FVA2
