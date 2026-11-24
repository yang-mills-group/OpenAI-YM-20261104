import YM.LocalLTE.FieldPT.Cinders
/-!
 Cut prices. No $photo$ lineage matching possible here without preserving views and roster. Rates for all arms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n L : Side} {j z k m i:ℕ} {W κ K U C V t H u v: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene
variable {a:RegularAddress n}(X:Art a z)(p:BudgetPoint)(f:ℝ→Pot G n)(s:ℝ)
-- actual integer PT grading
noncomputable def basisC (L: J k)(d: Fin m) := L.val+d.val -- k denominator shifts
lemma windsH (d:ℕ)(ε:ℝ)(he:0< ε) : ∃ v w:ℝ, -(1/2:ℝ)<v∧ v<w∧ w<0∧ v < Sienna.vow∧ (w+1/2)*d< ε:= by
    let y:ℝ:= min (1/100:ℝ) (ε/(10+2*d)); have hz:0<y:= lt_min (by norm_num) (by positivity)
    have h:y≤1/100:=min_le_left ..; have hp:y*(10+2*d)≤ε:= (le_div_iff₀ (by positivity)).mp (min_le_right ..)
    refine ⟨-(1/2)+y,-(1/2)+2*y,?_,?_,?_,?_,?_⟩
    all_goals first | (unfold vow; linarith) | linarith
structure PhotoJ (X: Art a z) (s:ℝ)(y ε:ℝ) (p:BudgetPoint)(f:ℝ→ Pot G n)(κ C:ℝ)(k i:ℕ) : Prop where
   isScene : Scene X.grove κ X.radius k i f C
   rebates (t: J k) (u: Fin i): (t.val+u.val<k → Scene.kernelF X.grove f u.val X.radius t=0) ∧
       p.supBounds a.site a.support (Weft.mark k t s • Price.banner X f κ t u) (C*y^(((k:ℝ) - (t.val:ℝ) - u.val )/2 +ε))
-- includes negative-bit valuation leaf costs, even though null! P.Power norm on clover.
lemma starsΩ {G:Gauge}{L:Side}{T:ℝ→ℕ}(hf:Rate G L 0 fun x=>(T x:ℝ))(g e k n:ℕ)(hp:Reliable G κ K){ε:ℝ}(he:0<ε) : ∀ᶠ x in atTop,∀ (c:Side)(P:BudgetPoint),P.threshold= Pressure.temp x → P.threshold≤2*Pressure.fiery G x L→P.order=g→P.power=e→∀ (a:RegularAddress c)(z:ℕ)(X:Art a z), z ≤ T x→ 32*z<c.val → ∀ (f:ℝ→ Pot G c)(C:ℝ),Scene X.grove κ X.radius k n f C→ ∀ b:ℝ, let v:=betaF G x L; v/2≤b→ b≤2*v → PhotoJ X (gStep b) v ε P f κ C k n:=by
    have h (d:ℕ) (j:J k): ∃ V P:ℝ→ℝ, ∀ᶠ x in atTop, let ζ:= betaF G x L; let p₀:ℝ:= (∑ i:J k,|slate k i j|/(probe k i)^d); let e':= ((k:ℝ)- j.val-(d:ℝ))/2+ε -- edit shadow order e. target envelope * norm*.
                         |V x| *p₀* |P x| ≤ ζ^e' ∧ (∀ b:ℝ,ζ/2≤ b→b≤2*ζ→ |Weft.mark k j (gStep b)| ≤ |V x|) ∧ ∀ (c:Side)(p:BudgetPoint), p.threshold=Pressure.temp x → p.threshold≤2*Pressure.fiery G x L →p.order=g→p.power=e→∀(z:ℕ)(a:RegularAddress c)(A:Art a z),z≤ T x→32*z<c.val→ ∀ u: Tensor.T (Directions G c) ℝ d,p.supBounds a.site a.support (play A κ u) (‖u‖* |P x|):=by
       obtain ⟨v,u,hv,h,hq,hw,hK⟩:= windsH d ε he
       obtain ⟨B,hB,H⟩:= magnify G L hf hp hv h hq hw g e d
       obtain ⟨V,hV,hΞ⟩:= hatCost G L j
       let p₀:ℝ:= ∑ i:J k,|slate k i j|/(probe k i)^d
       refine ⟨V,B,?_⟩
       filter_upwards [H,hΞ, ((Brim.absolut hV|>.mul_right p₀).mul (Brim.absolut hB)) (((k:ℝ)- j.val-(d:ℝ))/2+ε) (by linarith only [hK])] with x hx H hv ζ p' e'
       exact ⟨(le_abs_self _).trans hv,fun b hb hy=>(H b hb hy).trans (le_abs_self _),hx⟩ -- edit
    choose P V H using h
    filter_upwards [eventually_all.mpr fun j=>eventually_all.mpr (fun i:Fin n=> H i.val j)] with x h c p hp' he hi hZ a z X hT hN f C hs b v hv ht
    refine ⟨hs,fun j u=>?_⟩; let T:= Scene.kernelF X.grove f u.val X.radius j; obtain ⟨hz,hθ⟩:= Scene.subPrice X.grove f u.val X.radius p hs hp u.isLt j
    obtain ⟨h',hC,hF⟩:= h j u
    have hp'' := AnalyticBridge.CouplingShape.sup_scale (Weft.mark k j (gStep b)) (hF c p hp' he hi hZ _ a X hT hN T)
    refine ⟨hθ,sup_le hp'' (?_)⟩
    apply le_trans (mul_le_mul (hC _ hv ht) (mul_le_mul_of_nonneg_right hz (abs_nonneg _)) (by positivity) (abs_nonneg _)); apply _root_.le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h' hs.price); ring -- edit
end YM.AnalyticBridge.VerifiedReset.Collection.Price
