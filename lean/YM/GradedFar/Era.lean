import YM.GradedFar.Coffer
import YM.GradedFar.Earn
/-!
# Homogeneous adjustment at the *original measured coupling* in the physical tower

C5 positions are true continuum estimates (on exactly the hypothesized W) at this precursor; use
ClassExpansion after it and never have to change its aperture in doing the proof at the given x,f-grid.
Does not claim that the physical mesh comparison of section C has been proven.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
namespace Playbill
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open Fork (Sold Safe)
open Tickets
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J P:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n m h p:ℕ} {t:ℝ→ℝ}
local notation "V" => Sec G h
variable {X I : Type*} {u:Filter X} {W:X→I→Prop} {B:X→I→ℝ} {r:X→ℝ} {z:X→I→Points n}
local notation "g∴" => strength G
variable (hr:Tendsto r u trail) (ht:Coupling G t) (A:Safe u W B (fun _ _=>1))
local notation "t₁"=> t ∘ r
local notation "T₁"=> WithTax p u W B t₁
-- Exact frame difference map here for physical P=H with J the W frame. Cost input should be paid
-- at actual H. by known expansions. Include all coordinates in the same normalization.
def adjust_map (r:ℝ)(h:ℕ) := ((assign P r h).trans (assign J r h).symm).toLinearMap
def widens (h:ℕ) (t:ℝ→ℝ):Prop:= ∀ i:Toon G h,∀ v:Sec G h, Expansion t trail (fun r=> coord i (adjust_map J P r h v)) (attends Z v i)
lemma fixed_today (r:ℝ)(x:Points n)(v:ListInput G n h): frank F P none h r x v= frank F J none h r x (fun i=> adjust_map J P r h (v i)) := by
 rw [frank_use,frank_use]; apply congrArg; funext i; change (⟨h,_⟩:S.Tag)=⟨h, assign J r h ((assign J r h).symm (assign P r h (v i)))⟩; rw [LinearEquiv.apply_symm_apply]

include hr ht A H
theorem paidH (hw:widens J P Z h t)(hp:Portal F J Z u W r z t h p)(hZ:∀ v:ListInput G n h, Prospects u W B
    (fun i j=> sent Post h (z i j) v))(v:ListInput G n h): T₁ (fun x i=> frank F P none h (r x) (z x i) v)
      (fun x i=> sent Post h (z x i) v):=by
 let k:= change_coins hr ht A (hG:=hG); let w(x:X):ListInput G n h:= fun i=> adjust_map J P (r x) h (v i)
 have ha(i:Toon G h)(v:Sec G h): T₁ (fun x j=> coord i (adjust_map J P (r x) h v)) (fun _ _=> attends Z v i) := by
    have he:= hw i v; obtain ⟨C,hC,hA⟩:= (he.good p).cost; exact ⟨fun i=>Fork.Sold.closed _, Fork.Sold.bounded hC
       ((hr.eventually hA).mono fun x hx i _=> hx ())⟩
 simp_rw [fixed_today F J P,basis_sum (frank F J none _ _ _) (fun i=> adjust_map J P _ _ (v i)), multipliers,smul_eq_mul, adjust_compare]
 exact WithTax.sum k _ fun i _=> WithTax.mul k (WithTax.product k _ (fun _ _=> ha ..)) (paidW F Z M H hr ht A hp hZ (basisWord i))

omit hr A
variable (t)
-- First QScale common-cap compact expectation, from C5 on these compact layouts & hypotheses,
-- not requiring any operator expansion in the binding except that of the actually incorporated H-stand.
-- Note stock conventions in C5 from the supplier include the necessary finite basis current purchases.
def fixedPose (h n:ℕ): Prop:= ∀ K:Set (Points n), IsCompact K → K⊆conf n → ∀ k:ℕ, Portal F J Z trail
    (fun (_:ℝ) (_:↥K)=>True) id (fun _ x=>x.val) t h k
lemma stationary (hw:widens J P Z h t)(hp:fixedPose F J Z t h n) : ClassExpansion F P Post t n h:=by
    intro K hK hx v; have hZ (u:ListInput G n h) (k:ℕ): ∃ C:ℝ,0≤C ∧ ∀ x:↥K, ‖coeff k (sent Post h x.val u)‖ ≤ C:=by
      obtain ⟨c,h⟩:= hK.exists_bound_of_continuousOn ((kernel_continuous Z M H u k).mono hx)
      exact ⟨max 0 c, le_max_left .., fun j=>by rw [sent,coeff_mk]; exact (h _ j.property).trans (le_max_right ..)⟩
    refine ⟨fun i=> FVA2.GradedFar.Cart.Charge.cap ?_,fun k=>?_⟩
    · obtain ⟨C,hC,Y⟩:= hZ v i; exact ⟨C,Y⟩
    let w:= fun (_:ℝ) (_:↥K)=> True; have hv:Safe trail w (fun _ _=>1) (fun _ _=> (1:ℝ)):= Eventually.of_forall (fun _ _ _=>⟨le_rfl,zero_le_one⟩)
    have HZ(u:ListInput G n h): Prospects trail w (fun _ _=>1) (fun (_:ℝ) (x:↥K)=> sent Post h x.val u):=by
       intro k; obtain ⟨C,hC,H⟩:=hZ u k; exact Fork.Sold.bounded hC (Eventually.of_forall fun i p _=> (H p).trans_eq (mul_one _).symm)
    obtain ⟨k,c,hc,H'⟩:= (paidH F J P Z M H tendsto_id ht hv hw (hp K hK hx k) HZ v).error
    exact ⟨c,hc,H'.mono (fun i hi j=>by simpa only [Function.comp_apply,id_eq,one_pow,mul_one] using hi j trivial)⟩

-- moving variant: only grid coded here
variable {U B:ℝ}
local notation "P∥"=> moving G U B
def GridPose (K:Set (Points n))(N:Set (Points m))(h:ℕ)(U B:ℝ)(p:ℕ) := ∀ K' N',
    IsCompact K'→K' ⊆ conf n→ IsCompact N'→N' ⊆ Outside m→ K ⊆ interior K'→N ⊆ interior N'→
    ∀ j:ℕ, 1≤j→ ∃ W:Calendar→ Set (Points (n+m)), Crosser.Coverage G U B K N W j ∧
      Portal F J Z (moving G U B) (fun p x=> x∈ W p ∧ Crosser.Access K' N' p x) Prod.fst
        (fun _ x=>x) t h p
lemma corridor {K:Set (Points n)}{N:Set (Points m)}(hw:widens J P Z h t)(hp:GridPose F J Z t K N h U B p) :
    Crosser.GridPower F P K N t U B Post h p:= by
 intro K' N' hK hx hN hz hh hh' j hj; obtain ⟨W,H',Hv⟩:= hp K' N' hK hx hN hz hh hh' j hj
 refine ⟨ W,H',?_⟩; let w:= fun (p:Calendar) (x:Points (n+m))=> x∈ W p∧Crosser.Access K' N' p x
 intro v; have hy (v:ListInput G (n+m) h) : Prospects P∥ w (fun p _=>Δlog p) (fun p (x:Points (n+m))=>sent Post h x v) := fun k=>
    Road.formal_bill Z M H hK hx hN hz (z:=fun p x=>x) (fun p i (h:w p i)=> h.2) k v
 obtain ⟨k,C,hC,hp⟩:= (paidH F J P Z M H rising ht Road.safety hw Hv hy v).error
 refine ⟨k,C*2^(p+1),by positivity,?_⟩; filter_upwards [hp,poses (clock_budget hG ht),moneySafe] with p' hp hv h v' hx
 specialize hp v' hx; apply le_trans hp; let x:=g∴ p'.1; obtain ⟨he,hh,hh'⟩:=hv
 refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hh' (p+1))
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans h) _))) ?_
 exact le_of_eq (by ring)
end Playbill
end YM.Integration.GradedFar.Tariff
