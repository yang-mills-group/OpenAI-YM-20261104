import YM.GradedFar.Park
/-!
# Variation proof inputs from the trial/purchase and exact compact reading

Discharge valuation & substitution prices. Can infer even leading for any tested kernel without
travelling on the longer moving window. Use `stripe` to normalize engineering powers in the
variation equation.
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
local notation "Θ" => GroupS.ψ (WilsonPrescription.criterion Z) M ν
local notation "γ" => fun (T:ℝ)=> -Real.log T
local notation "TT"=> fun (i:Route)=> Θ (γ (stretch i))
variable {p q n h:ℕ}
local notation "V"=> Sec G h
variable {t:ℝ→ℝ}(ht:Coupling G t) (hC:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)

def φPred (p:ℕ)(t:ℝ→ℝ)(i:Route) : ℝ:= (appointedH140Crop p (t i.1) (TT i)).re
local notation "ωk" => φPred Z M ν

include H ht
lemma ancestor (p:ℕ) (A:PowerSeries ℂ) : ∃ C:ℝ,0≤C ∧ ∀ᶠ i in clock,
    ‖appointedH140Crop p (ωk p t i) A - appointedH140Crop p (t i.1) (A.subst (TT i))‖ ≤ C*(strength G i.1)^(p+1):=by
 let K:=Joggle × {s:ℂ//‖s‖≤1}; let f(k:K):= Θ (γ k.1.val); let L(k:K):ℝ:=0; let y(k:K):= k.2.val
 have he: Charge L (fun k:K=> (γ k.1.val:ℂ)) := by obtain ⟨C,hC,H⟩:= no_drag logHat; exact Charge.cap ⟨C,fun i=> H i.1⟩
 have hi: Beyond (p+1) y L (fun k=> operation p (operation p (y k) (ofPS (f k))) (ofPS A) - operation p (y k) (substitute (f k) (ofPS A))):=
    Cart.omitted_interpose (c:=f) p (f:=fun k=>ofPS A) (fun i=> Charge.const _) (Neighbor.days_cost Z M ν H he)
      (fun i=> ((H.dilation ν).check.led _).start) (Charge.cap ⟨1,fun i=>i.2.property⟩)
 obtain ⟨k,H'⟩:= hi.bound.exists; obtain ⟨C,hC,HV⟩:= ((eventually_ge_atTop 0).and H').exists -- shadow
 refine ⟨C*2^(p+1),by positivity,?_ ⟩; filter_upwards [running.eventually (clock_budget hG ht)] with i hh
 rw [op_crop,φPred, real_ψ Z M ν H (appointedH140Crop p (t i.1) (TT i)) (t i.1) p (γ (stretch i)) rfl, op_crop, op_crop]
 have hx: ∀ j, ofPS (A.subst (TT i)) j= substitute (TT i) (ofPS A) j := by intro j; rw [← Constants.actual_subst _ _ ((H.dilation ν).check.led _).start]; exact coeff_mk ..
 rw [funext hx]; obtain hz:= HV ((i.2,⟨(t i.1:ℂ),by rw [Complex.norm_real]; exact hh.2.1⟩):K)
 change ‖_‖ ≤ C*(1+|(0:ℝ)|)^k*‖(t i.1:ℂ)‖^(p+1) at hz; simp only [abs_zero, add_zero,one_pow,mul_one, Complex.norm_real] at hz
 exact hz.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (_:ℝ)) hh.2.2 _) hC).trans_eq (by ring))
lemma φZero (p:ℕ): Tendsto (ωk p t) clock (𝓝 0):= by
    have hu(k:ℕ)(q:ℕ): ∃ C:ℝ,0≤C ∧ ∀ i:Route,‖coeff k ((TT i)^q)‖≤ C:=by
       obtain ⟨C,hC,h⟩:= no_drag (Neighbor.days_cost Z M ν H logHat q k); exact ⟨C,hC,fun i=>h i.2⟩
    have ht'(k:ℕ): Tendsto (fun i:Route=> (t i.1:ℂ)^k*coeff k (TT i)) clock (𝓝 0):=by
       by_cases hk:k=0; · subst k; simp only [pow_zero,((H.dilation ν).check.led _).start,one_mul]; exact tendsto_const_nhds
       obtain ⟨C,hC,H⟩:= hu k 1; simp_rw [pow_one] at H
       apply squeeze_zero_norm' (a:=fun i=> |t i.1|^k*C)
       · exact Eventually.of_forall fun i=> by rw [norm_mul,norm_pow, Complex.norm_real]; exact mul_le_mul_of_nonneg_left (H i) (by positivity : 0 ≤ ‖t i.1‖^k)
       simpa [zero_pow hk] using ((((Coupling.conforms hG ht).comp running).abs.pow k).mul_const C)
    have he: Tendsto (fun i:Route=> appointedH140Crop p (t i.1) (TT i)) clock (𝓝 0):=by
       simp_rw [crop_eq]; simpa using tendsto_finsetSum (Finset.range (p+1)) (fun i _=> ht' i)
    exact Complex.continuous_re.continuousAt.tendsto.comp he
omit H ht
local notation "U'" => fun (r s:ℝ)=> LinearEquiv.toLinearMap (relative J r s h)
noncomputable def bearing (i:Route)(h:ℕ)(x:Stage n) : MultilinearMap ℂ (fun _:Fin n=> Sec G h) ℂ:=
    (frank F J none h i.1 (stretch i • x.val)).compLinearMap (fun _ :Fin n=> Level.Dial h (γ (stretch i)))
noncomputable def asset (h:ℕ)(i:Route):= (relative J i.1 (next i) h).toLinearMap
noncomputable def stripe (h:ℕ)(i:Route) := (Level.Dial h (Real.log (stretch i)))*asset J h i
noncomputable def bFare (h:ℕ)(t:ℝ→ℝ)(p:ℕ)(i:Route): Sec G h →ₗ[ℂ] Sec G h := ∑ k∈Finset.range (p+1), ((t i.1:ℝ):ℂ)^k • coeff k (KΛ (γ (stretch i)) h)
lemma active (i:Route): Level.Dial h (γ (stretch i)) * stripe J h i = asset J h i:= by rw [stripe, ← mul_assoc,Level.group, neg_add_cancel,Level.flat,one_mul]
lemma bFare_stamp (i:Route) (p:ℕ) (t:ℝ→ℝ): Neighbor.stamp G h (bFare Z M ν h t p i) = fare Z M ν h p (γ (stretch i)) (t i.1):= by simp only [bFare,fare,operation,firm,map_sum,map_smul]
lemma gear_bill (i:Route)(p:ℕ)(t:ℝ→ℝ): Level.Dial h (γ (stretch i)) * bFare Z M ν h t p i = cropK KΛ (γ (stretch i)) p (t i.1) h:= by
    simp only [bFare,Finset.mul_sum,cropK,conversion,coeff_C_mul,mul_smul_comm]
lemma bearing_use (i:Route)(x:Stage n)(v:ListInput G n h) : bearing F J i h x (fun j=> stripe J h i (v j)) = frank F J none h (next i) x.val v:= by
    have he (v:Sec G h): Level.Dial h (γ (stretch i)) (stripe J h i v)= relative J i.1 (next i) h v:=
       DFunLike.congr_fun (active J i (h:=h)) v
    change frank F J none h i.1 (stretch i • x.val) (fun j=> Level.Dial h (γ (stretch i)) (stripe J h i (v j)))=_
    simp_rw [he]; rw [frank_use,frank_use]
    rw [show next i=i.1*stretch i from rfl,mul_smul]; simp_rw [atHome]

lemma bearing_pay (i:Route)(x:Stage n)(u:ListInput G n h)(p:ℕ) (t:ℝ→ℝ): bearing F J i h x (fun j=> bFare Z M ν h t p i (u j)) =
    frank F J none h i.1 (stretch i • x.val) (fun j=> cropK KΛ (γ (stretch i)) p (t i.1) h (u j)):=by
    conv_rhs=> rw [← gear_bill Z M ν i p t];
    rfl

local notation "g∴" => strength G
private lemma lane (p q r:ℂ): ‖p-q‖ ≤ ‖p-r‖ + ‖r-q‖:= by simpa only [sub_add_sub_cancel] using norm_add_le (p-r) (r-q) 
include ht hC
include hG in
lemma boarded (x:Stage n)(u:ListInput G n h)(p:ℕ): ∃ C:ℝ,0≤C ∧ ∀ᶠ i in clock,
    ‖bearing F J i h x (fun j=> stripe J h i (u j)) - appointedH140Crop p (t (next i)) (sent Post h x.val u)‖ ≤ C*g∴ i.1^(p+1):=by
    obtain ⟨C,hC,H⟩:= ((hC {x.val} isCompact_singleton (singleton_subset_iff.mpr x.property) u).good p).cost
    refine ⟨C*4^(p+1),by positivity,?_⟩; filter_upwards [nextPath.eventually H,fees ht (hG:=hG)] with i h hv
    rw [bearing_use]; exact (h ⟨x.val,Set.mem_singleton x.val⟩).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hv _) hC).trans_eq (by ring))
include hG H
lemma board_expands (x:Stage n)(u:ListInput G n h)(p:ℕ): ∃ C:ℝ,0≤C ∧ ∀ᶠ i in clock,
    ‖bearing F J i h x (fun j=> bFare Z M ν h t p i (u j)) - appointedH140Crop p (ωk p t i) (sent Post h x.val u)‖ ≤ C*g∴ i.1^(p+1):=by
 obtain ⟨C,hC,H0⟩:= prepaid F J Z M ν H ht hC x u p -- shadow local hC
 obtain ⟨K,hK,H⟩:= ancestor Z M ν H ht p (sent Post h x.val u)
 refine ⟨C+K,add_nonneg hC hK,?_ ⟩; filter_upwards [H0,H] with i hr hv; rw [bearing_pay]; rw [norm_sub_rev] at hv
 exact (lane _ _ (appointedH140Crop p (t i.1) ((sent Post h x.val u).subst (TT i)))).trans ((add_le_add hr hv).trans_eq (add_mul ..).symm)
end YM.Integration.GradedFar.Tariff.Billboard
