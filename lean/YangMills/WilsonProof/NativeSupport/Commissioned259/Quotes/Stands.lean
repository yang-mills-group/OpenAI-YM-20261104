import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Lamps
import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Enroll
import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Paired
/-! # BB trial is *near* identity in the actual W-coordinates. Quantitative lower price
needs enrollment; not differentiating in r. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d} (t:ℝ→ℝ)
    (hJ:Leading U J) (P:Realized J Y N A t) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "LX" => guardTrial N ν M
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "ψ" => GroupS.ψ N.criterion M ν

variable (paid:Calibrated G t) {r T:I→ℝ}(hr:Tendsto r L late)(ht:∀ᶠ i in L,T i∈ Icc 1 2) (hQ: Mixture U J N d)
local notation "η" => Quotes.post T
local notation "f₂" => (fun i:I=>r i*T i)
local notation "ρ" => (t∘r)
abbrev L' (d:ℕ)(s:ℝ)(p:ℕ)(t:ℝ) := accepts (LX s d) p t
lemma columns_mul (A T: FieldEnd G d) : columns (A*T)= columns A * columns T:= Eq.symm (Comparing.composition' A T)
include paid hr ht H P
lemma rumor_note (p:ℕ) : Notes L Pose.home ρ (δ ∘ r) p Pose.home (fun i=> L' N ν M d (η i) p (ρ i)) (fun i=> LX (η i) d) := Notes.for_crop (delivered N ν M H ht)
lemma rumor_charge (p:ℕ) : Issue L Pose.home (fun i=> columns (L' N ν M d (η i) p (ρ i))) := matrixPay.mpr (fun i j=> homebound (Coin.costs (hr.eventually ((coupling_payment sim paid).mono fun i hi=>hi.2.1))
    (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (one_paid L) (rumor_note J Y N t P ν M H paid hr ht p i j) ))
lemma rumor_heads (p:ℕ) : Issue L (δ ∘ r) (fun i=> columns (L' N ν M d (η i) p (ρ i)) - engine G d (η i)) := by
  refine matrixPay.mpr fun a b=> ?_; have hp:= homebound (Tunes.excess (one_paid L)
    (hr.eventually ((coupling_payment sim paid).mono fun i hi=>hi.2.1)) (peson J Y t M H P paid hr)
    p 0 (Nat.zero_le _) (delivered N ν M H ht (d:=d) a b))
  have he (i:I) : crop 0 (ρ i) (prose (guardTrial N ν M (η i) d) a b) = engine G d (η i) a b := by
    rw [crop_apply,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,one_mul,prose,coeff_mk,trial_advance N ν M H]
  exact hp.congr (fun i=>by change _-crop 0 ((t∘r) i) (prose (LX (η i) d) a b)= columns (accepts _ _ _) _ _ - _; rw [he, Charge]; rfl) (fun i=> by simp [Pose.home])
-- actual trial at both radii through d
abbrev STrial (d:ℕ)(r T:ℝ)(p:ℕ) := (personal J Y (r*T) r d).toLinearMap * L' N ν M d (-Real.log T) p (t r)
local notation "R'" => (fun i:I=>personal J Y (f₂ i) (r i) d)
abbrev Zgear (T: I→ℝ)(i:I)(d:ℕ) : FieldEnd G d:= Level.Dial (G:=G) d (Quotes.post T i)
abbrev Dgear (T:I→ℝ)(i:I)(d:ℕ) : FieldEnd G d:= Level.Dial (G:=G) d (Real.log (T i))
abbrev parallel (i:I)(T r:I→ℝ)(d:ℕ) := personal J J (r i) (r i*T i) d
abbrev pstar (i:I)(T r:I→ℝ)(d:ℕ) := Zgear T i d * (parallel J i T r d).symm.toLinearMap
omit P paid ht hr H
lemma Z_D (i:I) : (Zgear (G:=G) T i d)* Dgear T i d=1:= Level.spring _
lemma D_Z (i:I) : (Dgear (G:=G) T i d)* Zgear T i d=1:= Level.autumn _
lemma reverse_flow (i:I) : columns (peter J d (r i) (T i)) * columns (pstar J i T r d)=1:= by
  let Y := parallel J i T r d; change columns (Y.toLinearMap * Dgear T i d)* columns (Zgear T i d * Y.symm.toLinearMap)=_; rw [ ← columns_mul, mul_assoc, ← mul_assoc (Dgear T i d), D_Z, one_mul, show Y.toLinearMap* Y.symm.toLinearMap= (1:FieldEnd G d) from (LinearMap.ext fun v=>( Y.apply_symm_apply v)) ]; exact one_matrix
include hJ hQ H hr ht in
lemma pstar_lim : Tendsto (fun i=>columns (pstar J i T r d)) L (𝓝 1):= unity ( (leading_step U J N hJ M H hQ).comp (hr.prodMk (tendsto_principal.mpr ht)) ) (Eventually.of_forall fun i=>reverse_flow J i)

include P hr
lemma receipt_trial (p:ℕ) : ∀ᶠ i in L, columns (STrial J Y N t ν M d (r i) (T i) p) =
    columns (Dgear (G:=G) T i d) * ((columns (pstar J i T r d) * columns (stand (A d ((t∘r) i)))) * columns (L' N ν M d (Quotes.post T i) p ((t∘r) i))) := by
  filter_upwards [hr.eventually (P.relates d)] with i hi
  let s:=r i*T i; let X:=frame J s d; have h : ( R' i).toLinearMap = Dgear T i d * ( pstar J i T r d * stand (A d ((t∘r) i))) := by
    unfold pstar; rw [mul_assoc, ← mul_assoc, D_Z, one_mul]
    apply LinearMap.ext; intro v
    exact congrArg X.symm (hi v)
  change columns ((R' i).toLinearMap * (L' N ν M d _ _ ((t∘r) i)))=_
  rw [h]; simp_rw [columns_mul,mul_assoc]
-- op contraction only
omit P hr
lemma close {F : Filter I}{t:I→ℝ}{A Z:I→Operator G d} (h:Tendsto A F (𝓝 1))
    (ht:∀ᶠ i in F,t i∈Icc 1 2)(hf:Issue F Pose.home Z)(hp:Shrinks F (fun i=>Z i-columns (Zgear t i d))):
    Tendsto (fun i=>columns (Dgear t i d) * (A i * Z i)) F (𝓝 1) := by
  have hh: Shrinks F (fun i=> A i* Z i-columns (Zgear t i d)) := by
    simpa only [one_mul] using (contraction_hyp (shrink h) hp (Issue.coverage (tendsto_const_nhds (x:=(1: Operator G d)))) hf)
  have eq : (fun i=> columns (Dgear (G:=G) t i d))=fun i=> engine G d (-(Quotes.post t i)) := by simp only [Dgear, Quotes.post, neg_neg]
  have hP : Issue F Pose.home (fun i=> columns (Dgear (G:=G) t i d)) := eq.symm ▸ eng_up ht
  apply esc_contract; exact Tendsto.congr (fun i=> by rw [mul_sub, ← columns_mul,D_Z]; exact congrArg ( _ - · ) one_matrix ) (shrink_l hP hh)
include H P ht hr paid
include hQ hJ in
lemma stand_lead (p:ℕ) : Tendsto (fun i=> columns (STrial J Y N t ν M d (r i) (T i) p)) L (𝓝 1) := by
  let X i:=columns (pstar J i T r d); let W i:= columns (stand (A d ((t∘r) i))); let G i:=columns (L' N ν M d (Quotes.post T i) p ((t∘r) i))
  have h : Tendsto (fun i=> X i* W i) L (𝓝 1):= by
    have h:= (pstar_lim U J N hJ M H hr ht hQ).mul ( young J Y t M H P paid hr )
    rw [mul_one] at h; exact h
  obtain e:= close (Z:=G) h ht (rumor_charge J Y N t P ν M H paid hr ht p)
    (shrink_into (rumor_heads J Y N t P ν M H paid hr ht p (d:=d)) ((g0_zero sim).comp hr))
  refine e.congr' ?_; exact (receipt_trial J Y N t P ν M hr p).mono (fun i hi=>hi.symm)

include hJ
lemma granted (p:ℕ) : ∀ᶠ i in L, Allowed (STrial J Y N t ν M d (r i) (T i) p) := by
  filter_upwards [hr.eventually (reapply U J Y N t hJ P d),(later_G hr ht sim).1.eventually (earnings U J hJ d)] with i h j
  exact allowed_product (owns U J Y j h) (trialAllowed N ν M H _ _ _)
def invoice (d:ℕ)(r T:ℝ)(p:ℕ) : Change G d := let x:=STrial J Y N t ν M d r T p; if h: Allowed x then ⟨x-1,h⟩ else 0
include paid
lemma voted (p:ℕ) : ∀ᶠ i in L, stand (invoice J Y N t ν M d (r i) (T i) p)=STrial J Y N t ν M d (r i) (T i) p := by
  filter_upwards [granted U J Y N t hJ P ν M H paid hr ht p (d:=d)] with i hi; unfold invoice; dsimp only; rw [dif_pos hi,stand]; dsimp only; abel
include hQ
lemma yours (p:ℕ) : Tendsto (fun i=>guide G d (invoice J Y N t ν M d (r i) (T i) p)) L (𝓝 0) := by
  refine ensign _ ( (stand_lead U J Y N t hJ P ν M H paid hr ht hQ p).congr' ?_ ); exact (voted U J Y N t hJ P ν M H paid hr ht p).mono (fun i hi=> congr_arg columns hi.symm)
end YM.FVA2.GradedFar259.Quotes
