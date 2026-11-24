import YM.WilsonCoeffUV.Test.Derivatives
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Votes have honest kme signed derivative measures
Compact cell * finite order/Axis/sign; no inf over actual labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Embroider.Canvas
open Filter Function Set Lattice RG MeasureTheory
open scoped Topology BigOperators ContDiff BoundedContinuousFunction ENNReal CompactlySupported
variable {D:ℕ}

abbrev Spun (D):= (Bool × Knob D) × Chamber
scoped instance (D:ℕ): MeasurableSpace (Spun D):=borel _
scoped instance (D:ℕ): BorelSpace (Spun D):=⟨rfl⟩
def positiveP (b:Bool): ℝ := if b then 1 else -1
lemma pointV (p:Bool): ‖positiveP p‖ = 1:= by cases p <;> simp [positiveP]

abbrev Easel (D) := ContinuousMap (Spun D) ℝ

def piece (D) : (ℝ× Volume D)→ₗ[ℝ] Easel D where
    toFun X:= ⟨fun x=> X.1 + positiveP x.1.1 * X.2.val x.1.2 x.2,by
       have he: Continuous (fun x:Spun D=>positiveP x.1.1):= (continuous_of_discreteTopology (f:=positiveP)).comp (continuous_fst.comp continuous_fst)
       have hg (i: Bool×Knob D):Continuous fun x:Chamber=> X.2.val i.2 x:= ContinuousMap.continuous _
       -- by local eventual fixing of first part
       refine continuous_const.add (he.mul (continuous_iff_continuousAt.mpr fun (x:Spun D)=> ?_))
       have hh: (fun v:Spun D=> X.2.val v.1.2 v.2) =ᶠ[𝓝 x] fun v => X.2.val x.1.2 v.2:= by
          filter_upwards [(continuous_fst.tendsto x).eventually (show ∀ᶠ y in 𝓝 x.1,y=x.1 by rw [nhds_discrete]; simp)] with y hy
          rw [show y.1=x.1 from hy]
       exact ((hg x.1).comp continuous_snd).continuousAt.congr hh.symm⟩
    map_add' _ _:= by ext v; simp [mul_add]; ring
    map_smul' c x:= by ext v; simp; ring

lemma price (a:ℝ × Volume D): ‖a.1‖+‖a.2‖ ≤ ‖piece D a‖:=by
   have H (b:Bool× Knob D)(v:Chamber): ‖a.1+positiveP b.1*a.2.val b.2 v‖≤ ‖piece D a‖:= ContinuousMap.norm_coe_le_norm (piece D a) (b,v)
   have hx b v: ‖a.1‖+‖a.2.val b v‖≤ ‖piece D a‖:=by
       have hu := H (true,b) v; have hv:= H (false,b) v
       simp [positiveP,Real.norm_eq_abs] at hu hv ⊢; grind
   let i : Knob D := ⟨0,(fun _=>0)⟩
   have h : ‖a.1‖ ≤ ‖piece D a‖:= le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hx i zeroC)
   linarith [show ‖a.2‖ ≤ ‖piece D a‖-‖a.1‖ from vote_cap _ (by linarith) (fun b v=> by linarith [hx b v])]

-- optionally manually shorten instance search on C(K)
private def nib (v:Vote D) : ℝ×Volume D →ₗ[ℝ] ℝ where
    toFun x:= ‖v‖*x.1+v x.2
    map_add' a b:=by simp [mul_add]; ring
    map_smul' a x:= by simp; ring

lemma big_nib (v:Vote D)(x:ℝ × Volume D): ‖nib v x‖ ≤ ‖v‖*‖piece D x‖:=by
   change ‖‖v‖*x.1+v x.2‖ ≤ _
   refine (norm_add_le _ _).trans ((add_le_add ?_ (v.le_opNorm x.2)).trans (show ‖v‖*‖x.1‖+‖v‖*‖x.2‖≤ _ from by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (price x) (norm_nonneg _)))
   exact le_of_eq (by rw [norm_mul,norm_norm])

local instance : NormedAddCommGroup (Easel D):=inferInstance
local instance : NormedSpace ℝ (Easel D):=inferInstance
local instance : NormedAddCommGroup (LinearMap.range (piece D)):=inferInstance
local instance : NormedSpace ℝ (LinearMap.range (piece D)):=inferInstance
lemma dressed (v:Vote D):∃ A:Easel D →L[ℝ]ℝ,(∀ a,A (piece D a)=nib v a)∧‖A‖≤ ‖v‖:=by
   obtain ⟨f,hf,hv⟩:= factoring (piece D).rangeRestrict (nib v) (LinearMap.surjective_rangeRestrict _) _ (norm_nonneg v) (show ∀ x, ‖nib v x‖≤‖v‖*‖(piece D).rangeRestrict x‖ from big_nib v)
   obtain ⟨g,hg,hr⟩:= exists_extension_norm_eq (LinearMap.range (piece D)) f
   exact ⟨g,fun x=> (hg ((piece D).rangeRestrict x)).trans (hf x),hr.le.trans hv⟩
lemma alive {M:ℝ}(A:Easel D →L[ℝ]ℝ)(h:A 1=M)(hp:‖A‖≤ M):Monotone A:=by
   have hx (f:Easel D)(hf :0≤ f): 0≤ A f :=by
       let V:= ‖f‖ • (1:Easel D)-f
       have he: ‖V‖≤‖f‖:= (ContinuousMap.norm_le V (norm_nonneg _)).mpr fun x=>by
           have hh:0≤f x:=hf x
           have ht:= le_trans (le_abs_self (f x)) (ContinuousMap.norm_coe_le_norm f x)
           simp [V,Real.norm_eq_abs]; rw [abs_le]; constructor <;> linarith [norm_nonneg f]
       have hk : A V ≤ M * ‖f‖:= le_trans (le_abs_self (A V)) ((A.le_opNorm V).trans (mul_le_mul hp he (norm_nonneg _) ((norm_nonneg A).trans hp)))
       simp [V,h] at hk; nlinarith
   intro f g H
   simpa using hx (g-f) (show 0≤g-f from fun x=> sub_nonneg.mpr (H x))

private abbrev CCE (D):= CompactlySupportedContinuousMap (Spun D) ℝ

def balk (p:Scroll D)(x:Spun D):= positiveP x.1.1*crease p x.1.2.2 x.2.val

lemma issued (v:Vote D):∃ A:Measure (Spun D), A.Regular ∧ IsFiniteMeasure A ∧ A.real univ=‖v‖ ∧ ∀ f:Scroll D,v (page _ f)=∫ x, balk f x ∂A:=by
    obtain ⟨g,h,hv⟩:=dressed v
    have he:piece D (1,0)=1:=by ext x; simp [piece]
    have hM : g 1=‖v‖:=by rw [←he,h]; simp [nib]
    let Λ: CCE D →ₚ[ℝ] ℝ := {
       toFun x:=g x.toContinuousMap
       map_add' x y:= map_add g x.toContinuousMap y.toContinuousMap
       map_smul' r x:= map_smul g r x.toContinuousMap
       monotone' _ _ h:= alive g hM hv h}
    let A:= RealRMK.rieszMeasure Λ
    let U (x:Easel D): CCE D:= ⟨x,HasCompactSupport.of_compactSpace _⟩
    have hr (x:Easel D): (∫ y,x y ∂A)=g x:= RealRMK.integral_rieszMeasure Λ (U x)
    refine ⟨A,inferInstanceAs (RealRMK.rieszMeasure Λ).Regular, inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure Λ)),?_,fun p=>?_⟩
    · rw [←hM,←hr]; simp
    have hp (x:Spun D): balk p x=piece D (0,page D p) x:= by simp [balk,piece,draft]
    simp_rw [hp,hr,h]; simp [nib]
end YM.WilsonCoeffUV.Embroider.Canvas
