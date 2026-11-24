import YM.GradedFar.Splice
import YM.GradedFar.Taffy
/-!
# Polynomial variation for G1

Leading companion required: same real permitted frame motion across those apertures, tends
to identity at leading. This is the earlier qualitative physical input of QScale before the
positive-order (G.1). `Held` states it on those exact operands. It's not a quantitative
positive-order assertion. Venue of its origin/binder hypotheses is separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill FVA2.GradedFar.Cart
open Tickets
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ){hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "KΛ" => GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν
local notation "γ" => fun (T:ℝ)=> -Real.log T
variable {n h:ℕ}
local notation "V"=> Sec G h
variable {t:ℝ→ℝ}(ht:Coupling G t) (hC:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
local notation "Φ"=> bFare Z M ν h
local notation "A'"=> stripe J h
local notation "mark"=> Neighbor.stamp G h
local notation "phi"=> φPred Z M ν
structure Held (J:ℝ→tower S)(h:ℕ):Prop where
    cheap : Tendsto (fun p=> Neighbor.stamp G h (stripe J h p)) clock (𝓝 1)
    permitted : ∀ᶠ i in clock, stripe J h i-1∈Normalize.Change G h
local notation "E" => Normalize.Change G h
-- for splice stability don't have to show full-r asym expansion of Held matrices yet
lemma hold (h:ℕ)(hh:Held J h)(v:Sec G h): Tendsto (fun i=>columns G h (stripe J h i v)) clock (𝓝 (columns G h v)):=by
    simp_rw [← stamped]; exact ((ContinuousLinearMap.apply ℂ (Sheet G h) (columns G h v)).continuous.tendsto (1:Operation G h)).comp hh.cheap
include H
lemma free_b (t:ℝ→ℝ) (i:Route): Φ t 0 i=1:= by
 have hx:= ((H.dilation ν).check.paid (γ (stretch i)) h).zero; rw [bFare,Nat.zero_add, Finset.sum_range_one,pow_zero,one_smul,hx]
include ht in
lemma lighten (v:V)(p:ℕ): Tendsto (fun i=> columns G h (Φ t p i v)) clock (𝓝 (columns G h v)):=by
 have hx(k:ℕ): ∃ C:ℝ,0≤ C ∧ ∀ i:Route, ‖columns G h (coeff k (KΛ (γ (stretch i)) h) v)‖ ≤ C:=by
    obtain Hθ:=Neighbor.field_cost Z M ν H h logHat k; obtain ⟨C,hC,k,Hθ⟩:= Hθ
    refine ⟨C*width v,mul_nonneg hC (width_nn _),?_⟩; intro i; specialize Hθ i.2
    simp only [abs_zero,add_zero,one_pow,mul_one] at Hθ; exact (op_use _ _).trans (mul_le_mul_of_nonneg_right Hθ (width_nn v))
 have hu : Tendsto (fun i:Route=> (t i.1:ℂ)) clock (𝓝 0):= ((Complex.continuous_ofReal.tendsto 0).comp ((Coupling.conforms hG ht).comp running)) -- defeq
 simp_rw [bFare, Finset.sum_range_succ'] -- aim leading + constants
 -- simplify
 simp only [LinearMap.add_apply,map_add,map_sum,LinearMap.sum_apply, LinearMap.smul_apply, map_smul, pow_zero, one_smul, ((H.dilation ν).check.paid _ h).zero,
     Module.End.one_apply]
 have hg(k:ℕ): Tendsto (fun i:Route=> (t i.1:ℂ)^(k+1) • columns G h (coeff (k+1) (KΛ (γ (stretch i)) h) v)) clock (𝓝 0) := by
   obtain ⟨C,hC,h⟩:=hx (k+1); refine squeeze_zero_norm' (a:=fun i=> ‖(t i.1:ℂ)‖^(k+1)*C) (Eventually.of_forall ?_) ?_
   · intro i; rw [norm_smul,norm_pow]; exact mul_le_mul_of_nonneg_left (h i) (by positivity)
   simpa using ((hu.norm.pow (k+1)).mul_const C)
 simpa using (tendsto_finsetSum (Finset.range p) (fun i _=> hg i)).add_const (columns G h v)

lemma b_legal (p:ℕ) (i:Route)(t:ℝ→ℝ) : (Φ t p i)-1∈ E:= by
 induction p with
 | zero=>
    rw [free_b Z M ν H, show (1: V→ₗ[ℂ] V) - 1 = 0 from by ext1 p; exact sub_self p]; exact (E).zero_mem
 | succ p ih =>
    let a:= coeff (p+1) (KΛ (γ (stretch i)) h); obtain hx:= ((H.dilation ν).check.paid (γ (stretch i)) h).high (p+1) (by omega)
    let f := (⟨Φ t p i-1,ih⟩:E); let g :=(t i.1)^(p+1) • (⟨a,hx⟩:E)
    have he : Φ t (p+1) i-1=(f+g).val:= by
       ext1 x; unfold bFare; rw [Finset.sum_range_succ,← Complex.ofReal_pow]; change (Φ t p i x+ (_:ℂ) • a x)-x=(Φ t p i x-x)+ (_:ℝ) • a x
       have hr(c:ℝ): c • a x=(c:ℂ) • a x:= Subtype.ext ((Maxwell.Free.volumes ..).symm)
       rw [hr]; abel
    exact he ▸ (f+g: E).property

def switchValue (i:Route)(h p:ℕ)(t:ℝ→ℝ):= stripe J h i-bFare Z M ν h t p i
theorem stays (t:ℝ→ℝ)(p:ℕ)(hA:Held J h): ∀ᶠ i in clock,switchValue J Z M ν i h p t∈ E:= by
 filter_upwards [hA.permitted] with i hi
 let A:E:=⟨A' i-1,hi⟩; let B:E:=⟨Φ t p i-1,b_legal Z M ν H p i t⟩
 rw [show switchValue J Z M ν i h p t=(A-B:E).val from by
      ext1 x; change A' i x-Φ t p i x=(A' i x-x)-(Φ t p i x-x); abel]; exact Subtype.property _

include ht hC ν
lemma bearing_lower (x:Stage n)(u:ListInput G n h): Tendsto (fun i=> bearing F J i h x u) clock (𝓝 (iris x u)):= by
 obtain ⟨C,hC,H₀⟩:= board_expands F J Z M ν H ht hC x u 0; simp_rw [free_b Z M ν H, crop_eq, sent, coeff_mk,declared, dif_pos x.property,
    Nat.zero_add, Finset.sum_range_one,pow_zero,one_mul,lead0 Z M H,pow_one] at H₀
 refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (g:=fun i:Route=> C*strength G i.1) (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ ?_)
 exacts [H₀, (by simpa only [Function.comp_apply,Route,mul_zero] using (((Coupling.conforms hG (strength_coupling hG)).comp running).const_mul C))]
lemma bearing_tends (x:Stage n){u:Route→ListInput G n h}{v:ListInput G n h}(he:∀ i,Tendsto (fun p=> columns G h (u p i)) clock (𝓝 (columns G h (v i)))) :
    Tendsto (fun p=> bearing F J p h x (u p)) clock (𝓝 (iris x v)):=by
 rw [basis_sum (iris x) v]
 simp_rw [basis_sum (bearing F J _ h x) (u _),smul_eq_mul]; apply tendsto_finsetSum; intro i _
 exact (tendsto_finsetProd Finset.univ (fun j _=> tendsto_pi_nhds.mp (he j) (i j))).mul (bearing_lower F J Z M ν H ht hC x _)
end YM.Integration.GradedFar.Tariff.Billboard
