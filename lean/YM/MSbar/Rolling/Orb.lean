import YM.MSbar.Rolling.Clarity
import YM.MSbar.Folia.Script
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set
open Next.SectorChange Further.GaussianScalar Push.Uniform
open RG Lattice Wilson Precision Tree Bakery Bakery.Film Metric
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge} {ι:Type}[Fintype ι][DecidableEq ι]
local notation "X"=> Positions (ι × G.ColorIndex)
local notation "ℳ"=>MeasureTheory.Measure
variable (J:ChartRatio G)(v:Positions (ι × G.ColorIndex))(h:LocalRatio J) {A r:ℝ}
-- choose trunc absolute scalar.B(E).µ centered, w state at mean+gr.
noncomputable def kerf (x:ℝ) (y: X):LinkArray G ι:=release (1:LinkArray G ι) (tape (x • y))
def urn (A x:ℝ): Set (LinkArray G ι):= kerf x '' Metric.closedBall 0 A
def den (v:X)(A:ℝ):Set X:={u | ‖v+u‖≤A}
local notation "Y"=> urn (G:=G) (ι:=ι)
set_option quotPrecheck false
local notation "V"=> tape (G:=G) (ι:=ι)
local notation "χ"=> pay J
lemma paints (x:ℝ) (y:X): tape (G:=G) (x •y) =tint G _ (x • y):=rfl
include h
lemma domain (hx:0<r)(hk:shade G*(r*A)<J.radius)(u:X)(he:‖u‖≤ A): V (r•u)∈mouth J:=by
    rw [paints]; intro i _; rw [Metric.mem_ball,dist_zero_right]; refine (norm_le_pi_norm _ _).trans_lt (((tint_le _).trans ?_).trans_lt hk); rw [norm_smul,Real.norm_of_nonneg hx.le]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx.le) (shade_pos G).le
lemma hung (hx:0<r)(hk:shade G*(r*A)<J.radius) : ribbonD id (1:LinkArray G ι) J (r•v) (urn A r) r= den v A:=by
    ext y; constructor
    · rintro ⟨⟨z,hz,hh⟩,he⟩; have hp:release (1:LinkArray G ι) (V (r•z))= release (1:LinkArray G ι) (V (r•v+r •y)):=hh
      have hu:(r•z)=(r•v+r •y):= tape.injective (release_injOn h _ (domain J h hx hk z (by simpa using hz)) he hp)
      rw [← smul_add] at hu; change ‖v+y‖ ≤ _; rw [← smul_right_injective _ hx.ne' hu]; simpa using hz
    intro hu; change _∈Y A r ∧ _; rw [← smul_add]; exact ⟨⟨v+y,(by simpa [den] using hu),rfl⟩,domain J h hx hk _ hu⟩
-- use generic exposed with F=0, test x weights. λ=chart cost *pay at 0; intend divide.Phi
variable (K:Matrix (ι × G.ColorIndex) (ι × G.ColorIndex) ℝ)(hp:K.PosDef)
def capitalJ (J:ChartRatio G) (v:Positions (ι × G.ColorIndex)) := Real.log (pay J (tape v))-Real.log (pay J (0:LogArray G ι))
def capitalF (j:ChartRatio G)(r:ℝ)(z:ℝ)(h:LinkArray G ι→ℝ) (p:X) := Real.log (h (kerf r (v+p)))+capitalJ j (r•(v+p))+dotProduct p (K *ᵥ p)/2+z
def exitS (k:Matrix (ι × G.ColorIndex) (ι × G.ColorIndex) ℝ)(J:ChartRatio G) := modeCost k⁻¹ *pay J (0:LogArray G ι) -- precedence cost k ⁻¹?
lemma crispG :0<pay J (0:LogArray G ι):=Finset.prod_pos fun _ _=>mul_pos h.scale (h.pos _ (mem_ball_self h.patch))
include hp
lemma perk : 0<exitS K J:=mul_pos (modeCost_pos hp.inv) (crispG J h)
local notation "Kδ"=>fieldLaw (K⁻¹)
lemma mint (z:ℝ)(F:LinkArray G ι→ℝ)(hx:0<r)(hk:shade G*(r*A)<J.radius)(hg:Envelope F)(hh:∀ i,0<F i):
    Integrable (Portal.purse (den v A) (capitalF v K J r z F)) (fieldLaw K⁻¹) ∧
    (∫ i in urn A r,F i∂ piHaar G ι)=r^(Fintype.card (ι × G.ColorIndex))*exitS K J * Real.exp (-z)*(∫ i,Portal.purse (den v A) (capitalF v K J r z F) i∂fieldLaw K⁻¹):=by
    let C:= K⁻¹
    let X₀:= urn (G:=G) (ι:=ι) A r; let O:= (0:LinkArray G ι→ℝ); let L:= (1:LinkArray G ι); let H:= fieldLaw (K⁻¹); have hu:X₀ ⊆ covered J L:=by
        rw [← release_image]; rintro x ⟨y,hv,rfl⟩; exact ⟨_,domain J h hx hk y (by simpa using hv),rfl⟩
    have hi: MeasurableSet X₀:= by
        have hc : Continuous (kerf r (G:=G) (ι:=ι)):= (release_continuous ..).comp ((tint G _).continuous.comp (show Continuous (fun x:X=>r•x) from by fun_prop))
        exact ((isCompact_closedBall ..).image hc).measurableSet
    obtain ⟨ht,hζ⟩:= exposed (G:=G) (α:=LinkArray G ι) (ι:=ι) id L J h (r•v) K⁻¹ X₀ F O hp.inv hi measurable_id (by exact Envelope.const _) hg hu hx
    -- re-expression.
    let k:= pay J (0:LogArray G ι); let K':= k* Real.exp (-z); let w(i:X):=Portal.purse (den v A) (capitalF v K J r z F) i
    let ζ(i:X):=Portal.purse (ribbonD id L J (r•v) X₀ r) (clipT id L J (r•v) K⁻¹ r O) i*F (id (spruce L r (r •v) i)); have hY :ribbonD id L J (r•v) X₀ r=den v A:= hung J v h hx hk
    have he(i:X) : ζ i=K'*w i:=by
        unfold ζ w Portal.purse; by_cases hz:i∈den v A
        · rw [Set.indicator_of_mem (show i∈ribbonD _ _ _ _ _ _ from hY.symm ▸ hz),Set.indicator_of_mem hz]; let W:=kerf r (v+i); let u:=pay J (tape (r•(v+i)))
          have H: C⁻¹=K:=Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _|>.mp hp.isUnit)
          have hp :0 < u:= Finset.prod_pos fun j _=>mul_pos h.scale (h.pos _ ((domain J h hx hk _ hz) _ (Set.mem_univ _)))
          have hk:k>0:=crispG J h
          unfold clipT capitalF capitalJ; simp only [← smul_add]; rw [show (K⁻¹)⁻¹=K from H]
          let q:=dotProduct i (K *ᵥ i)/2; have he:id (spruce L r (r • v) i) = W:=by unfold spruce; rw [←smul_add];rfl
          rw [he]; change Real.exp (0 + Real.log u+q)*F W=K'*Real.exp (Real.log (F W)+(Real.log u-Real.log k)+q+z)
          have hL:=hh W; unfold K'; simp_rw [Real.exp_add,Real.exp_neg,Real.exp_sub,Real.exp_log hp, Real.exp_log hL, Real.exp_log hk,Real.exp_zero]; field_simp
        rw [Set.indicator_of_notMem (show i∉ribbonD _ _ _ _ _ _ from fun h=> hz (hY ▸ h)),Set.indicator_of_notMem hz,zero_mul,mul_zero]
    have hv :0<K':=mul_pos (crispG J h) (Real.exp_pos _)
    have hG:Integrable (fun i=> K'* w i) (fieldLaw K⁻¹) :=by simp_rw [← he]; exact ht
    refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hv.ne') _).mp hG,?_⟩
    rw [← integral_indicator hi]; have hF:X₀.indicator F= palette X₀ id O F:= by ext1 x; unfold palette O; simp
    rw [show (urn A r).indicator F=_ from hF,hζ]; change _*(∫ i,ζ i∂ _) = _; simp_rw [he]; rw [integral_const_mul]; unfold K' k w exitS; ring
end YM.MSbar.Rolling
