import YM.GradedFar.Liability
import YM.GradedFar.Soft
/-!
# Formal step-by-step price exercise

Through m (= `p` here) accuracy eventually over the entire interval of
ratios induced by power of home coupling. Require coupling-calendar rate relative to g,
not uniform over clocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h p:ℕ)
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "g"=> strength G
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p
local notation "γ" => fun (T:ℝ)=> -Real.log T
variable {t:ℝ→ℝ}(ht:Coupling G t){U B:ℝ}(hU:0<U)(hB:0<B)

lemma id_cost : ‖(1:Operation G h)‖ ≤ 1:= ContinuousLinearMap.norm_id_le
lemma short_bill {x:ℝ}(hx:x∈ Icc (1:ℝ) 2): |γ x| ≤ |Real.log 2|:= by
 rw [abs_neg,abs_of_nonneg (Real.log_nonneg hx.1)]; exact
   (Real.log_le_log (zero_lt_one.trans_le hx.1) hx.2).trans (le_abs_self ..)

include hU hB ht H
private lemma constants (hp:1≤p): ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ T,Wide G U B r T →
    let t0:ℂ:=t r
    ‖B' (γ T) t0-1‖ ≤ C*g r ∧ ‖J' (γ T) t0 - t0‖ ≤ C*g r ∧
    ∀ x:ℝ,x∈ Icc (1:ℝ) 2 → ‖B' (γ T) t0 * B' (γ x) (J' (γ T) t0) - B' (γ (T*x)) t0‖ ≤ C*(g r)^p ∧
      ‖J' (γ x) (J' (γ T) t0)-J' (γ (T*x)) t0‖ ≤ C*(g r)^p:=by
 obtain ⟨C,hC,k,hk⟩:= budget_up Z M ν h p H hp (Real.log 2); have hc:0<C:=zero_lt_one.trans_le hC
 let b:= C*2^(p+1); refine ⟨b,by dsimp only [b]; positivity,?_⟩; filter_upwards [clock_budget hG ht, pay_log (hG:=hG) hU hB k] with r hr hv T hT
 obtain ⟨hg,ht,ht'⟩:=hr; rw [← Real.norm_eq_abs,← Complex.norm_real] at ht ht'
 specialize hv T hT; let u:=γ T; let H0:= hk u; let t0:ℂ:= t r
 have he(n:ℕ)(hn:n≤p): C*(1+|u|)^k*‖t0‖^(n+1) ≤ b*(g r)^n:=by
   have h: |u|=Real.log T:= by dsimp only [u]; rw [abs_neg,abs_of_nonneg (Real.log_nonneg hT.1)]
   have hx:= Real.log_nonneg hT.1; unfold b; rw [h]
   calc
     _ ≤ C*(1+Real.log T)^k*(2*g r)^(n+1):=by gcongr
     _ = C*2^(n+1)*( (1+Real.log T)^k*g r)*(g r)^n:=by ring
     _ ≤ C*2^(p+1)*1*(g r)^n := by gcongr; linarith
     _ = _:= by rw [mul_one]
 dsimp only; have ho:=he 1 hp; rw [pow_one] at ho; have hz:= H0 0 t0 (by rw [abs_zero]; exact abs_nonneg _) ht
 refine ⟨hz.1.trans ho,hz.2.1.trans ho,?_⟩; intro x hx; obtain ⟨H,h'⟩:= (H0 (γ x) t0 (short_bill hx) ht).2.2
 have H₀ : γ (T*x)=u+γ x:= by dsimp only [u]; rw [Real.log_mul (zero_lt_one.trans_le hT.1).ne' (zero_lt_one.trans_le hx.1).ne',neg_add]
 -- notation β applied invisibly
 specialize he p le_rfl; change ‖fare _ _ _ _ _ _ _ * _ - B' (γ (T*x)) t0‖ ≤ _ ∧ ‖J' _ _ - J' (γ (T*x)) t0‖ ≤ _
 rw [H₀]; exact ⟨H.trans he,h'.trans he⟩

-- demand at padded stretch T even in short leg that goes outside Wide eventually. applications go inside.
structure FormalPlan (t:ℝ→ℝ)(b r T:ℝ): Prop where
 eye : ‖B' (γ T) (t r)-1‖ ≤ 1/4
 cost : ‖B' (γ T) (t r)‖ ≤ 2
 surplus x(x1:x∈ Icc (1:ℝ) 2) : ‖B' (γ T) (t r)*B' (γ x) (J' (γ T) (t r)) - B' (γ (T*x)) (t r)‖ ≤ b
 corner x(x1:x∈ Icc (1:ℝ) 2) : ‖J' (γ x) (J' (γ T) (t r))-J' (γ (T*x)) (t r)‖ ≤ b
 transfer x(x1:x∈ Icc (1:ℝ) 2): ‖B' (γ x) (t (r*T))-B' (γ x) (J' (γ T) (t r))‖ ≤
        ‖(t (r*T):ℂ)-J' (γ T) (t r)‖
 hear x(x1:x∈ Icc (1:ℝ) 2): ‖J' (γ x) (t (r*T))-J' (γ x) (J' (γ T) (t r))‖ ≤
        2*‖(t (r*T):ℂ)-J' (γ T) (t r)‖
lemma paid (hp:1≤p): ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ T,Wide G U B r T → FormalPlan Z M ν h p t (C*g r^p) r T:=by
 obtain ⟨C,hC,hx⟩:= constants Z M ν h p H ht hU hB hp
 obtain ⟨δ,hδ,H'⟩:= ((show ∀ᶠ δ:ℝ in trail,0<δ from self_mem_nhdsWithin).and (jiffy Z M ν h p H (Real.log 2))).exists
 have ht':= Coupling.conforms hG ht
 have hc: Tendsto (fun r=> ‖(t r:ℂ)‖) trail (𝓝 0):= by
    simpa only [Complex.norm_real,norm_zero] using ht'.norm
 have hCC: Tendsto (fun r=> C*g r) trail (𝓝 0):=by
    simpa only [mul_zero] using ((Coupling.conforms hG (strength_coupling hG)).const_mul C)
 refine ⟨C,hC,?_⟩; filter_upwards [hx,hCC.eventually_le_const (by norm_num: (0:ℝ)<1/4),
    (show Tendsto (fun r=> C*g r + ‖(t r:ℂ)‖) trail (𝓝 0) from by simpa using hCC.add hc).eventually_le_const hδ,
    out_radius hG (U:=U) (B:=B) _ (hc.eventually_le_const hδ)] with r hr Hv HH hT T hA
 obtain ⟨u,t',hf⟩:=hr T hA; obtain hv:= u.trans Hv; specialize hT T hA.1 hA.2; let y:=γ T
 have hy: ‖B' y (t r)‖ ≤ 2:=by
   have hs:= norm_add_le (B' (γ T) (t r)-1) 1; rw [sub_add_cancel] at hs; linarith only [hv,hs,id_cost (G:=G) h]
 have hz: ‖J' y (t r)‖ ≤ δ:= by
   have hs:= norm_add_le (J' (γ T) (t r)-(t r:ℂ)) (t r:ℂ); rw [sub_add_cancel] at hs; linarith only [t',hs,HH]
 exact ⟨hv,hy,fun i hi=>(hf i hi).1,fun i hi=>(hf i hi).2,fun i hi=>(H' (γ i) _ _ (short_bill hi) hT hz).1,
   fun i hi=>(H' (γ i) _ _ (short_bill hi) hT hz).2⟩
end YM.Integration.GradedFar.Neighbor
