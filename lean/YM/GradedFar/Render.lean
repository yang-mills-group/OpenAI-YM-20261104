import YM.GradedFar.RateMark
/-!
# G1 pays BOTH measured clock and field at any cap

Even asking a different horizon h, include cap 6 in the measurement queries to price
relative t. These are receipts at every T ∈ [1/2,2]; spend before the longer itinerary.
Provide the unaddressed earlier qualitative hypothesis `Held` explicitly on the **same** H.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ){hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Φ" => bFare Z M ν
local notation "AΦ" => stripe J
local notation "V‴" => billΔ J Z M ν
variable (h p:ℕ)(t:ℝ→ℝ)
local notation "Ω"=> MoveSpace G h
local notation "Ω'" => Normalize.Change G h
local notation "g∴" => strength G
structure Question (G:Gauge)(h:ℕ): Type where
    n:ℕ
    x:Stage n
    v:ListInput G n h
-- generic second horizon
abbrev Forum (G:Gauge)(h d:ℕ) := Tick G h × MoveSpace G d
abbrev QType (G:Gauge)(h:ℕ):= Question G h⊕ Question G 6
def Speak.fst (G:Gauge)(h d:ℕ) : Forum G h d→ₗ[ℝ] Tick G h:= LinearMap.fst ℝ _ _
def Speak.snd (G:Gauge)(h d:ℕ): Forum G h d→ₗ[ℝ]Tick G d:=
    (((LinearMap.fst ℝ ℝ (MoveSpace G h)).comp (Speak.fst G h d))).prod (LinearMap.snd ℝ _ _)
def query (p:ℕ) (i:Route) (q: QType G h): Forum G h 6 →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap
    (match q with
    | .inl q=> (debit F J Z M ν p t q.x q.v i).comp (Speak.fst G h 6)
    | .inr a=> (debit F J Z M ν p t a.x a.v i).comp (Speak.snd G h 6))
def answer (q:QType G h): Forum G h 6→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap
    (match q with
    | .inl q=> (entry Z q.x q.v).comp (Speak.fst G h 6)
    | .inr a=> (entry Z a.x a.v).comp (Speak.snd G h 6))
lemma value_entry {x: Ω} (he:release G h x=0) : x=0:=by
 apply (guide G h).symm.injective; simp only [map_zero]; exact Subtype.ext he
include H
theorem Answer.zero (y: Forum G h 6) (hv:∀ q, answer Z h q y=0): y=0 := by
 let x:=y.1.1; let u:= release G h y.1.2; let v:= release G 6 y.2
 have h1 : ∀ n(z:Stage n)(w:ListInput G n 6), Manifest.response z w v = (x:ℂ)*Post 6 n z 1 w:= fun n z w=> sub_eq_zero.mp
    (show entry Z z w (x,y.2)=0 from hv (.inr ⟨n,z,w⟩))
 obtain ⟨h₀,hx⟩:= Billboard.stamp Z M H (A:=v) ((guide G 6).symm y.2).property h1
 have h2:u=0:=by
    apply Manifest.sure hG _ ((guide G h).symm y.1.2).property; intro n z v
    have hp: entry Z z (h:=h) v y.1=0:= hv (.inl ⟨n,z,v⟩); rw [entry_eval] at hp; change y.1.1=0 at hx; rw [hx,Complex.ofReal_zero,zero_mul,sub_zero] at hp; exact hp
 exact Prod.ext (Prod.ext hx (value_entry h h2)) (value_entry 6 h₀)
variable (hp:1≤p) (ht:Coupling G t) (hh:Held J h)(hh': Held J 6)
    (hκ:∀ n,ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
    (hξ:∀ n,ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n 6)
def wΔ (i:Route): Forum G h 6:= ((slide Z M ν p t i,billΔ J Z M ν p t i h),billΔ J Z M ν p t i 6)
include hp ht hh hh' hκ hξ
lemma shipment : ∃ C:ℝ,0 ≤ C ∧ ∀ᶠ i in clock,
    ‖wΔ J Z M ν h p t i‖ ≤ C*(g∴ i.1)^(p+1):= by
    let α:= answer Z h; let β:= query F J Z M ν h t p
    let w:= wΔ J Z M ν h p t; have hv(q) (v:Forum G h 6): Tendsto (fun i=> β i q v) clock (𝓝 (α q v)):=by
       rcases q with q|q
       · exact leading_debit F J Z M ν H p t q.x q.v ht hh (hκ _) hp v.1
       exact leading_debit F J Z M ν H p t q.x q.v ht hh' (hξ _) hp (v.1.1,v.2)
    have hq(q):∃ C:ℝ,0≤C∧∀ᶠ i in clock,‖β i q (w i)‖≤ C*g∴ i.1^(p+1):=by
       rcases q with q|q
       · exact individual F J Z M ν H p t q.x q.v ht hh (hκ _)
       exact individual F J Z M ν H p t q.x q.v ht hh' (hξ _)
    obtain ⟨s,C,hC,H⟩:= issued α (Answer.zero Z M H h) hv; choose z hz hz' using hq
    let r:=∑ i∈s,z i; have hr:0≤r:= Finset.sum_nonneg fun _ _=>hz _
    refine ⟨C*r, mul_nonneg hC hr,?_⟩; filter_upwards [H,(eventually_all_finset s).2 (fun t _=> hz' t), strength_positive hG |> running.eventually]
      with i hi he hr'
    have h: ‖(fun j:↥s=> β i j.val (w i))‖ ≤ r*strength G i.1^(p+1):= by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun j=> (he j.val j.property).trans ?_); exact
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hz i) j.property) (by positivity)
    exact (hi (w i)).trans ((mul_le_mul_of_nonneg_left h hC).trans_eq (mul_assoc ..).symm)

open Neighbor in
lemma award : DialStamp Z M ν t p := by
 obtain ⟨C,hC,H'⟩:= shipment F J Z M ν H h p t hp ht hh hh' hκ hξ; replace H':= everywhere.mp H'
 refine ⟨C,hC,H'.mono fun r he T hT=> ?_⟩; let i:Route:= (r,⟨T,hT⟩); let d:= appointedH140Crop p (t r) (GroupS.ψ Z.criterion M ν (-Real.log T)); change ‖(t (r*T):ℂ)-d‖≤ _; specialize he i.2
 rw [← (show (d.re:ℂ)= d from real_ψ Z M ν H d _ _ _ rfl), ← Complex.ofReal_sub, Complex.norm_real]; let v:=wΔ J Z M ν h p t i
 exact (norm_fst_le v.1).trans ((norm_fst_le v).trans he)

omit H ht hh hh' hp hκ hξ
-- need norm bound converting guide coords. includes no use of Leading Branch.
lemma deliver (G:Gauge)(h:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ v:MoveSpace G h,‖Neighbor.stamp G h (release G h v)‖ ≤ C*‖v‖:=by
 let f:= (Neighbor.stamp G h).restrictScalars ℝ ∘ₗ (release G h); exact ⟨‖f.toContinuousLinearMap‖,ContinuousLinearMap.opNorm_nonneg _,fun i=> f.toContinuousLinearMap.le_opNorm i⟩
lemma billOne (p:Route) : ‖stretching G h (-Real.log (stretch p))‖≤ (2:ℝ)^h:= by
    have ht:= stretch_pos p.2;
    refine stretch_limit (t:=-Real.log (stretch p)) (by positivity) ?_; intro i; unfold Extent.token; rw [neg_neg,Real.exp_log ht,norm_pow, Complex.norm_real,Real.norm_of_nonneg ht.le]; exact
      (pow_le_pow_left₀ ht.le p.2.property.2 _).trans (pow_le_pow_right₀ (by norm_num) (size_le i))
include H ht hh hh' hp hκ hξ
lemma charged : Stamp J Z M ν t h p:=by
 obtain ⟨b,hb,Hf⟩:= deliver G h; obtain ⟨C,hC,Hv⟩:= shipment F J Z M ν H h p t hp ht hh hh' hκ hξ
 have he:∀ᶠ i in clock, let F':= cropK (GroupS.gaugeN Z.scheme Z.criterion M ν) (-Real.log (stretch i)) p (t i.1) h;
                         opField (asset J h i-F')≤ 2^h*b*C*(g∴ i.1)^(p+1):=by
    filter_upwards [Hv,billing J Z M ν H p t hh] with i hA hx
    specialize Hf (billΔ J Z M ν p t i h); rw [hx] at Hf
    dsimp only; rw [show asset J h i - _ = Level.Dial h (-Real.log (stretch i))*switchValue J Z M ν i h p t from by unfold switchValue; rw [← active J i,← gear_bill Z M ν i p t]; ext1 x; exact ((Level.Dial h (-Real.log (stretch i))).map_sub (AΦ h i x) (Φ h t p i x)).symm, show ∀ (X:FieldEnd G h),opField X = ‖Neighbor.stamp G h X‖ from fun X=>rfl, Neighbor.price]
    let y:=wΔ J Z M ν h p t i; refine (norm_mul_le ..).trans ((mul_le_mul (billOne h i (G:=G)) Hf (norm_nonneg _) (by positivity)).trans ?_); exact le_trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((norm_snd_le y.1).trans ((norm_fst_le y).trans hA)) hb) (by positivity)) (le_of_eq (by ring))
 refine ⟨2^h*b*C,by positivity,(everywhere.mp he).mono (fun r hr t ht=> hr (⟨t,ht⟩:Joggle))⟩
end YM.Integration.GradedFar.Tariff.Billboard
