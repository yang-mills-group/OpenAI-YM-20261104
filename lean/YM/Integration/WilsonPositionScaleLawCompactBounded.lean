import YM.Integration.WilsonPositionScaleLawBounded
import YM.Integration.WilsonPositionScaleLawCompactIndependent

/-! A joint bound on genuine signed overflow products at every ratio on a prescribed positive compact interval. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactBounded
open Function Filter Set Finset PowerSeries MeasureTheory Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio)
open WilsonPositionScaleLawCompactNative (positive)
open WilsonPositionScaleLawIndependent (B scaleRows)
open WilsonPositionScaleLawCompactIndependent (continuousTime)
open private eval from YM.Integration.WilsonPositionScaleLawBounded
open WilsonPositionPrescribedAllocations (Assign amount rectangle low total)
open private weight from YM.Integration.WilsonPositionScaleLawHome
open scoped Topology BigOperators Classical
variable [Win:RangeSpec] {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

include H in
private theorem arm {d:ℕ}(k:ℕ)(v:Sec G d)(l:Module.Dual ℂ (Sec G d)):
    Continuous (fun t:Ratio=>l (Level.Dial d (WilsonPositionScaleLawCompactIndependent.time t) (coeff k (B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d) v))):=by
  let row(j:Fin (d+1)):Module.Dual ℂ (FieldEnd G d):=(l.comp (Level.proj j)).comp (eval v)
  have hc(j:Fin (d+1)):Continuous (fun t:Ratio=>Extent.token (WilsonPositionScaleLawCompactIndependent.time t) j • row j (coeff k (B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d))):=by
    have power:Continuous (fun t:Ratio=>Extent.token (WilsonPositionScaleLawCompactIndependent.time t) j):=by
      simp only [Extent.token,WilsonPositionScaleLawCompactIndependent.geometry]
      exact (continuous_pow j.val).comp (Complex.continuous_ofReal.comp continuous_subtype_val)
    exact power.smul ((WilsonPositionScaleLawIndependent.coefficient Z M H ν d k (row j)).comp continuousTime)
  simp only [Level.Dial,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  exact continuous_finsetSum univ (fun j _=>hc j)

include H in
theorem bounded {d n q:ℕ}(φ:Test n)(v:Fin n→Sec G d)(a:Assign n q):∃C:ℝ,0≤C ∧ ∀t:Ratio,
    ‖amount (B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d) (scaleRows Z M ν d (WilsonPositionScaleLawCompactIndependent.time t)) φ v a‖≤C:=by
  let U:=Measure.start Z.scheme Z.criterion d
  let input:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have study:=Jury.enrolled ν M Z.scheme Z.criterion σ hG input.Taylor input.still input.base (d:=d)
  let K:=tsupport φ
  letI : CompactSpace K:=isCompact_iff_compactSpace.mp φ.hasCompactSupport
  let X:=Ratio×K
  let y(z:X):=Facets.posing (WilsonPositionScaleLawCompactIndependent.time z.1) (⟨z.2.val,φ.tsupport_subset z.2.property⟩:Stage n)
  have cy:Continuous (fun z:X=>(y z).val):=by
    change Continuous (fun z:X=>Real.exp (-(WilsonPositionScaleLawCompactIndependent.time z.1)) • z.2.val)
    simp_rw [WilsonPositionScaleLawCompactIndependent.geometry]
    exact (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  let w(t:Ratio)(j:Fin n):=coeff (a (some j)).val (B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d) (v j)
  let u(t:Ratio)(j:Fin n):=Level.Dial d (WilsonPositionScaleLawCompactIndependent.time t) (w t j)
  let m(z:X):=U n (y z) (a none).val (u z.1)
  have cm:Continuous m:=by
    have point(b:Fin n→Dframe.Toon G d):Continuous (fun z:X=>U n (y z) (a none).val (Dframe.fill b)):=by
      have continuity:= (study.light n (a none).val (Dframe.fill b)).comp_continuous cy (fun z=>(y z).property)
      exact continuity.congr (fun z=>congrArg (fun f=>f (a none).val (Dframe.fill b)) (Jury.exactC U (y z)))
    have arms(b:Fin n→Dframe.Toon G d):Continuous (fun z:X=>Dframe.each b (u z.1)):=by
      change Continuous (fun z:X=>∏j,(MS.Theater.Daylight (Press.portDeck G) d).coord (b j) (u z.1 j))
      exact continuous_finsetProd _ (fun j _=>(arm Z M H ν (a (some j)).val (v j) _).comp continuous_fst)
    have expansion(z:X):m z=∑b:Fin n→Dframe.Toon G d,Dframe.each b (u z.1)*U n (y z) (a none).val (Dframe.fill b):=Dframe.stencil_he ..
    exact (continuous_finsetSum _ (fun b _=>(arms b).mul (point b))).congr (fun z=>(expansion z).symm)
  obtain ⟨P,hP⟩:BddAbove ((fun z:X=>‖m z‖) '' univ):=isCompact_univ.bddAbove_image cm.norm.continuousOn
  let count:=∫x,‖φ x‖
  have hc:0 ≤ count:=integral_nonneg fun _=>norm_nonneg _
  refine ⟨count*max 0 P,mul_nonneg hc (le_max_left _ _),?_⟩
  intro t
  let f(x:Points n):=Jury.fxt (Facets.scaling (WilsonPositionScaleLawCompactIndependent.time t) U) x (a none).val (w t)
  have tested:amount (B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d) (scaleRows Z M ν d (WilsonPositionScaleLawCompactIndependent.time t)) φ v a=φ.applyTo f:=
    (WilsonPositionScaleLawIndependent.original Z M H ν d (WilsonPositionScaleLawCompactIndependent.time t)).exact n (a none).val φ (w t)
  rw [tested]
  apply weight
  intro x hx
  have rz:f x=m (t,⟨x,hx⟩):=by
    change Jury.fxt (Facets.scaling (WilsonPositionScaleLawCompactIndependent.time t) U) x (a none).val (w t)=_
    have confx:x∈conf n:=φ.tsupport_subset hx
    exact congrArg (fun L=>L (a none).val (w t))
      (Jury.exactC (Facets.scaling (WilsonPositionScaleLawCompactIndependent.time t) U) (⟨x,confx⟩:Stage n))
  rw [rz]
  exact (hP (mem_image_of_mem _ (mem_univ ((t,⟨x,hx⟩):X)))).trans (le_max_right _ _)

include H in
theorem omitted {d n:ℕ}(q:ℕ)(φ:Test n)(v:Fin n→Sec G d):∃C:ℝ,0≤C ∧ ∀t:Ratio,∀g:ℝ,|g|≤1→
    let O:=B Z M ν (WilsonPositionScaleLawCompactIndependent.time t) d
    let K:=scaleRows Z M ν d (WilsonPositionScaleLawCompactIndependent.time t)
    ‖(∑k:Fin (q+1),(g:ℂ)^k.val*K k.val n φ (fun j=>∑b:Fin (q+1),(g:ℂ)^b.val • coeff b.val O (v j)))-
      ∑k∈range (q+1),(g:ℂ)^k*realm O K k n φ v‖≤C*|g|^(q+1):=by
  choose C hC price using fun a:Assign n q=>bounded Z M H ν φ v a
  refine ⟨∑a,C a,sum_nonneg (fun a _=>hC a),?_⟩
  intro t g hg
  dsimp only
  rw [rectangle,low,←sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _=>?_)
  by_cases h:total a≤q
  · simp only [if_pos h,sub_self,norm_zero]
    exact mul_nonneg (hC a) (pow_nonneg (abs_nonneg _) _)
  · simp only [if_neg h,sub_zero,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul (price a t) (pow_le_pow_of_le_one (abs_nonneg g) hg (by omega))
      (pow_nonneg (abs_nonneg _) _) (hC _)

end YM.Integration.WilsonPositionScaleLawCompactBounded
end
