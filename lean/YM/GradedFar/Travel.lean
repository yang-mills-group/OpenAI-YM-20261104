import YM.GradedFar.Ambient
/-!
# Application to first (M.2) under the physical estimates consumed by its proof

*conditional* on QScale's growing forecast & RoundMeter point hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries Source Extraction Table Spec Climb
open Trace.Pilot PhysMS FVA2 XSpace XSpace.Normalize Register Scale Dframe O O.Score O.Enh
open FVA2.GradedFar
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open OPE (Viewers)
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (P : ℝ → tower S)
variable {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (N : WilsonPrescription G) {hG : G.Simple}
    (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    (H : Main.Match N hG Z σ true) (ν : ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G

variable {t : ℝ → ℝ} (ht : Coupling G t) {Λ B : ℝ}
include hG in
lemma forecast_budget (h1 : ∀ i, FrameForecast P t W (e i) Λ B) (p : ℕ) :
    ∃ p' : ℕ, p+5 ≤ p' ∧ ∃ X D : ℝ, 1 ≤ X ∧ 0 ≤ D ∧ ∀ᶠ r in trail,
    ∀ T : ℝ, 1 ≤ T → T ≤ Λ*(g r)^(-B) → ∀ i,
      opField (relative P r (r*T) (e i)).toLinearMap ≤ X*T^(e i) ∧
      opField ((relative P r (r*T) (e i)).toLinearMap - cropK W (-Real.log T) p' (t r) (e i)) ≤ D*(g r)^(p+1) := by
  choose X hx hX using fun i => (h1 i).1
  have hf := eventually_all.mpr fun i => (h1 i).2 (p+2)
  obtain ⟨p',hs,hp'⟩ := (hf.and (eventually_ge_atTop (p+5))).exists
  choose D hd hD using hs
  obtain ⟨x,hb⟩ := Finite.exists_le X
  obtain ⟨y,hc⟩ := Finite.exists_le D
  refine ⟨p',hp',max x 1,max y 0,le_max_right .., le_max_right ..,?_⟩
  filter_upwards [eventually_all.mpr hD,eventually_all.mpr hX,strength_positive hG,
    (Coupling.conforms hG (strength_coupling hG)).eventually_le_const zero_lt_one] with r hr hx hP hs T hT ht i
  constructor
  · exact (hx i T hT ht).trans (mul_le_mul_of_nonneg_right ((hb i).trans (le_max_left ..)) (by positivity))
  · exact (hr i T hT ht).trans (mul_le_mul ((hc i).trans (le_max_left ..))
      (pow_le_pow_of_le_one hP.le hs (by omega)) (by positivity) (le_max_right ..))

variable {K : Set (Points n)} {S' : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
include H hK hx hS hy ht
lemma first_value (p : ℕ) (hd : Through l d) (he : Through l e)
    (hW : ∀ i, FrameForecast P t W (e i) Λ B) (funded : RoundPoint F P t A hd he Λ B p K S') :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ r in trail,
    ∀ T : ℝ, T₀ ≤ T → T ≤ Λ*(g r)^(-B) → ∀ x ∈ K, ∀ y ∈ S', ∀ o : E4,
    ∀ (ω : Viewers F) (u : Inputs G d) (v : Inputs G e), Box u 1 → Box v 1 →
      ‖atLength F P ω o r T x y u v - crop p (t r) (fullSeries A W (-Real.log T) hd he x y u v)‖ ≤
        M*T^(FVA2.GradedFar.power e)*(g r)^(p+1)*(1+Real.log T)^k := by
  obtain ⟨p',hp',X,D,hX,hD,hδ⟩ := forecast_budget P N (hG:=hG) Z ν hW p
  obtain ⟨Q,hQ,k,T₀,hT,H0⟩ := funded
  obtain ⟨M,hM,j,hj⟩ := sale hd he (H.separatedOPE ν).wilson (H.dilation ν).check
    hK hx hS hy (show p ≤ p' by omega) hX hQ hD k
  obtain ⟨T₁,h₁⟩ := eventually_atTop.mp hj
  have hf : Tendsto (fun r : ℝ => D*(g r)^(p+1)) trail (𝓝 0) := by
    simpa using ((Coupling.conforms hG (strength_coupling hG)).pow (p+1)).const_mul D
  refine ⟨M,hM.le,j,max T₀ T₁, le_trans hT (le_max_left ..),?_⟩
  filter_upwards [clock_budget hG ht, H0, hδ, hf.eventually_le_const zero_lt_one] with r hr h₀ hδ hq
  intro T hi hl x hxx y hyy o ω u v hu hv
  have hi' := le_trans (le_max_left ..) hi
  have h2 : 1 ≤ T := by linarith
  rw [relative_full]; exact h₁ _ ((le_max_right ..).trans hi) x hxx y hyy (t r) (g r) u v hr.1.le hr.2.1
    hr.2.2 hu hv hq (today F P ..) (fun v hv => h₀ T hi' hl x hxx y hyy o ω u v hu hv)
    (fun i => (relative P r (r*T) (e i)).toLinearMap) (fun i => (hδ T h2 hl i).1)
    (fun i => (hδ T h2 hl i).2)

theorem first (p : ℕ) (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    (hW : ∀ i, FrameForecast P t W (e i) Λ B) (hf : RoundPoint F P t A hd he Λ B p K S')
    (hout : RoundPoint F P t A (d:=Output h) (fun _ => hh) he Λ B p {0} S') :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ r in trail,
    ∀ T : ℝ, T₀ ≤ T → T ≤ Λ*(g r)^(-B) → ∀ x ∈ K, ∀ y ∈ S', ∀ o : E4,
    ∀ (ω : Viewers F) (u : Inputs G d) (v : Inputs G e), Box u 1 → Box v 1 →
      ‖atLength F P ω o r T x y u v - crop p (t r) (fullSeries A W (-Real.log T) hd he x y u v)‖ +
        rowPrice (atCenter F P h ω o r T y v - croppedResponse A W (-Real.log T) hh he y v p (t r)) ≤
        M*T^(FVA2.GradedFar.power e)*(g r)^(p+1)*(1+Real.log T)^k := by
  obtain ⟨M,hM,k,T₀,hT,H'⟩ := first_value F P N Z H ν ht hK hx hS hy p hd he hW hf
  obtain ⟨M',hm,j,T₁,h₁,hq⟩ := first_value F P N Z H ν ht (d:=Output h) isCompact_singleton
    (show {(0:Points 1)} ⊆ conf 1 from fun _ _ => (fun _ _ _ => Subsingleton.elim ..)) hS hy p _ _ hW hout
  refine ⟨M+M',add_nonneg hM hm,k+j,max T₀ T₁,le_trans hT (le_max_left ..),?_⟩
  filter_upwards [H',hq,strength_positive hG] with r hr hQ hu T hf hB x hxx y hyy o ω u v hU hV
  have hp : 2 ≤ T := hT.trans ((le_max_left ..).trans hf)
  have ht := Real.log_nonneg (show 1 ≤ T by linarith)
  have hd : 1 ≤ 1+Real.log T := le_add_of_nonneg_right ht
  apply le_trans (add_le_add (hr _ ((le_max_left ..).trans hf) hB _ hxx _ hyy o ω u v hU hV)
    (row_pay (C:= M'*T^(FVA2.GradedFar.power e)*(g r)^(p+1)*(1+Real.log T)^j) (by positivity) ?_))
  · rw [add_mul, add_mul, add_mul]; gcongr <;> omega
  intro a ha
  rw [LinearMap.sub_apply, center_length, croppedResponse_apply]
  exact hQ _ ((le_max_right ..).trans hf) hB 0 (Set.mem_singleton _) _ hyy o ω (fun _ => a) v
    ((boxes zero_le_one).mpr fun _=>ha) hV
end YM.Integration.GradedFar
