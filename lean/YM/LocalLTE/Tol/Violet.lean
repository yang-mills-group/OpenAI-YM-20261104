import YM.LocalLTE.Tol.Dove
/-!
# Real calibrated cylinder supplies. Hold section stencils including cover placement. All LABEL directions in calibrated canonical finite requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{d k:ℕ}
set_option quotPrecheck false
local notation "L"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
open Extra.Histories
variable {n:Side}(G d)(o:Site n)(b:ℕ)(κ:ℝ)(k)(i:((Labels.frames G).level d).Index)
local notation "f"=> (L).places (Size.axis F i) o
local notation "f'"=> Port.scaleQ false ∘ f
-- forces all source stencils on canon values. Actually F.act orientation pins assigned labels, real. 
lemma basisT : f=Hue 1 false ∘ (f'):=by
    funext U; let a : (F).Coeff:= Size.axis F i; have ho: Star.star a=a:=by
         funext j; unfold a Extra.Histories.Size.axis; by_cases h:j=i
         · rw [h]; simp
         simp [h] -- syntax
    have hh:= (Next.Foundations.sound G d|>.ordinary_real a (expandAt o U)); rw [ho] at hh
    change f U= Star.star (f U) at hh
    have hp:(f U).im=0:=by
       have hx := congr_arg Complex.im hh; simp only [RCLike.star_def,Complex.conj_im] at hx; linarith only [hx] -- star eq
    dsimp only [Function.comp_apply]; rw [Port.hueVal,one_mul,Port.ink,mul_one]; apply Complex.ext <;> simp [Port.scaleQ,hp]
local notation "S"=> (neighbors b o)
local notation "V"=> (neighbors (b+1) o)
variable (Z:Grove o)
def crestA := FrameBox.Hall.shave Z b κ k (Port.scaleQ false ∘ (localSection G d).places (Size.axis ((Labels.frames G).level d) i) o)
local notation "g"=> crestA G d k o b κ i Z
def yews := Hue 1 false ∘ (crestA G d k o b κ i Z)
local notation "W"=> (yews G d k o b κ i Z)
-- affine rank.All. D.Price. mechanism
lemma huesMoved (c:ℂ)(p:Bool)(m:ℕ)(hm:k≤ m+1) : AnalyticBridge.VerifiedReset.Collection.Price.Replicated Z b κ (m+1) (Port.scaleQ p ∘ (c • (W))):=by
    let t:ℝ:= (Port.scaleQ p) (c *Port.Hue 1 false 1)
    have he:(Port.scaleQ p ∘ (c • W))= t • g:=by
        funext U; change Port.scaleQ p (c* Hue 1 false (g U))= t * (g U); conv_lhs=>rw [show g U=g U • (1:ℝ) by simp]
        rw [map_smul, mul_smul_comm (g U) c, map_smul]; exact mul_comm _ _ -- edit
    rw [he]; exact AnalyticBridge.VerifiedReset.Collection.Price.rp_scale _ _ (AnalyticBridge.VerifiedReset.Collection.Price.rp_raise Z (show AnalyticBridge.VerifiedReset.Collection.Price.Replicated Z b κ k g from ⟨_,rfl⟩) hm)
variable (A:BudgetPoint){p j k':ℕ} {a x M:ℝ}(hp:A.power=p)(hj:A.order=j)(h0:(localSection G d).footprint o ⊆ neighbors b o)(hκ:Reliable G κ a)
local notation "P"=> Next.Foundations.price G (d+p+j)
include hp hj
lemma budge : A.Regular ((L).footprint o) f ∧ A.supBounds o ((L).footprint o) f P := by
    obtain ⟨h,hE⟩:= Next.Foundations.priced G (D:=d+p+j) (by omega : d ≤ d+p+j) (by omega: j ≤ d+p+j) (by omega: p ≤ d+p+j) A hj hp n o i
    refine ⟨h,⟨zero_le_one.trans (Next.Foundations.price_one_le ..),fun U hU v hv hP=> (hE.2 U hU v hv hP).trans ?_⟩⟩
    exact mul_le_of_le_one_right (zero_le_one.trans (Next.Foundations.price_one_le ..)) (pow_le_one₀ A.threshold_pos.le A.threshold_le)
include h0
lemma blue {X:ℝ}(h':P≤X) : A.Regular V f ∧ A.supBounds o V f X:=by
   have he:= budge G d o i A hp hj
   have hT: S ⊆ V:=by
       intro y hy
       exact (neighbors_mem ..).2 (((neighbors_mem ..).1 hy).trans (Nat.le_succ b))
   have hh:= Next.Foundations.bound_larger he.2 (h0.trans hT); exact ⟨Next.Foundations.regular_larger he.1 (h0.trans hT),hh.1.trans h',fun U hU l hl hv=>(hh.2 U hU l hl hv).trans h'⟩
include hκ
lemma woods (ht : A.supBounds o V (f' - g) x)(ha : P≤M) : A.Regular V W ∧ A.supBounds o V W (M+x) ∧ A.Regular V (f-W)∧ A.supBounds o V (f-W) x:=by
    have hu : S ⊆ V:=by
       intro y hy
       exact (neighbors_mem ..).2 (((neighbors_mem ..).1 hy).trans (Nat.le_succ b))
    have he:= blue G d o b i A hp hj h0 ha
    have hv: A.Regular V g:= AnalyticBridge.VerifiedReset.reg_larger (FrameBox.legal _ _ hκ _ _) hu
    let F0:=(f'); have hh:= Port.framesV he.1 he.2 false
    have hg: A.supBounds o V g (M+x):=by
         have h:= AnalyticBridge.VerifiedReset.sup_sub hh.1 (AnalyticBridge.VerifiedReset.reg_sub hh.1 hv) hh.2 ht
         rw [sub_sub_cancel] at h; exact h
    have hu1:= Port.hueRad g A V hv 1 false o hg
    have hG:=AnalyticBridge.VerifiedReset.reg_sub hh.1 hv
    have hX := Port.hueRad (F0-g) A V hG 1 false o ht
    rw [norm_one,one_mul] at hu1 hX
    refine ⟨Port.hueReg _ _ _ hv _ _, hu1,regular_sub he.1 (Port.hueReg _ _ _ hv _ _),?_⟩
    rw [basisT, yews, Port.hueDiff]; exact hX -- potential recursive f in θ
-- Event physical.J scaled real.Not assuming price.
omit hp hj hκ h0
variable (Xj:ℝ)(hK':Reliable G κ a)
include hK'
lemma accrual (hk: Xj < (k:ℝ)/4) : ∀ᶠ x:ℝ in atTop,∀ B:BudgetPoint,B.order=j→ B.power=p→ B.threshold=temp x → ∀ (n:Side),2*(b+1) < n.val →2*(2*b) ≤ n.val → ∀ (o:Site n), (L).footprint o⊆neighbors b o → ∀ Z:Grove o,B.supBounds o (neighbors (b+1) o) ((Port.scaleQ false ∘ (L).places (Size.axis F i) o) -(crestA G d k o b κ i Z)) (x^(-Xj)):=by -- parentheses comp precedence
    let Y:=oneQ; let v:= -(1/4:ℝ); let k':=fun _:ℝ=> b+1
    obtain ⟨u,hu,hV⟩:= Sect.authorityL (G:=G) d (k+j) i false -- order
    have hp:0+v*(k:ℝ)< -Xj:=by unfold v; linarith
    filter_upwards [FrameBox.Hall.prunes G Y j p k (n:=k') («g»:=fun _=>u) (by exact Rate.const ((b+1:ℕ):ℝ)) hK' (show -(7/16:ℝ) ≤ v by norm_num [v]) (show v < 0 by norm_num [v]) (Rate.const _) hp,eventually_ge_atTop (1:ℝ)] with x ht hx B hB he hx' n hn hK o hR Z
    have hv:∀ U: Directions G n,‖U‖< Inset.cone v (betaF G x Y) → Brush (k+j) (1*u) 1 ((Port.scaleQ false ∘ (L).places (Size.axis F i) o) ∘ FrameBox.Grove.soloV) U:=by
       rw [one_mul,show Y=oneQ from rfl,oneShift]; exact fun U h=> hV n o U (h.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (show v ≤ 0 by norm_num [v])))
    have hA:B.threshold ≤ 2*Pressure.fiery G x Y:=by unfold fiery; rw [← show oneQ=Y from rfl, oneShift,← hx']; linarith only [B.threshold_pos]
    have hh:= budge G d o i B he hB; have hr:= (Port.framesV hh.1 hh.2 false).1
    have hz:= ht B he hB hx' hA (b+1) b le_rfl le_rfl n o hn hK Z _ (AnalyticBridge.VerifiedReset.reg_larger hr hR) 1 zero_le_one hv; rwa [← show oneQ=Y from rfl,oneShift,one_mul] at hz
end YM.LocalLTE.Port.Sect
