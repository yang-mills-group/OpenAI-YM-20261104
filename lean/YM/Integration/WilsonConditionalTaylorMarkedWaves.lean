import YM.Integration.WilsonConditionalTaylorMarkedWidths
import YM.Integration.WilsonConditionalTaylorBulkPass

/-! Complete earlier Wilson vacuum in every connected fluctuation tiling
consulted by an occupied response, not only in the final unmarked log. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedWaves
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open WilsonConditionalTaylorBulkRows WilsonConditionalTaylorBulkShape
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (W : Pot G)
    (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : ∀ n, (primary P.patch K n).Choices)
    (U : (n : Side)→Pap (wire G n))

theorem all (hp : Vivid W) (hr : LocalRatio ρ) (room : 4≤t) (E : ℕ) (shape : ∀ n,Ranks (U n))
    (prior : ∀ a ≤ E, ∀ d, 0 < d → d ≤ E+2 → ∃ w : ℝ, 0 < w ∧
      Kith w (W a d) (fun n=>rancho (U n) a d)) :
    ∃ s : ℝ,0<s ∧ ∃ B : ℝ,0≤B ∧ (gamma G K P L h).strip s B ∧
      ∀ i a, a≤E → ∀ d,0<d → Kith s (magma P L W ρ h i a d)
        (fun n=>swim ((rayshot P L h).acts n) (rancho (inlet P L ρ h n (k n) (U (n*P.L)))) i a d) :=by
  let X:=cola W ρ P L K
  let Z(n : Side):=rancho (inlet P L ρ h n (k n) (U (n*P.L)))
  have raw(a : ℕ)(ha : a≤E)(d : ℕ)(hd : 0<d)(use : d≤E+2) :
      ∃ w:ℝ,0<w ∧ Kith w (X a d) (fun n=>Z n a d) :=by
    obtain ⟨s,pos,bill⟩:=prior a ha d hd use
    have B:1 ≤ (P.L.val:ℝ):=by exact_mod_cast P.L.property
    have fee : Kith s (altitude P.patch W a d) (fun n=>rancho (joust (unitSplit G (primary P.patch K n) 1) (U (n*P.L))) a d):=by
      simp only [joust_level]
      exact WilsonConditionalTaylorRetile.scaled P.L (τ:=s) (by nlinarith [mul_nonneg (sub_nonneg.mpr B) pos.le]) pos.le bill
    exact WilsonConditionalTaylorBulkInlet.sourced P L ρ h k (fun n=>U (n*P.L)) W hr room a d ⟨0,hd⟩ pos fee
  have torus(n):Fiery (Z n):=paid P L ρ h n (k n) _ hr room (shape _)
  obtain ⟨w,wp,purchased⟩:=WilsonConditionalTaylorMarkedWidths.vacuum (E:=E) (Bank.fairy W ρ P L K hp hr) torus raw
  obtain ⟨z,B,zp,strip⟩:=(gamma_ready G K P L h).1
  let s:=min z w
  have positive:0<s:=lt_min zp wp
  have B0:0 ≤ max 0 B:=le_max_left ..
  have geom:=(strip_mono strip (min_le_left z w) (le_max_right 0 B))
  let q:=rayshot P L h
  have dots (a d : ℕ) (hd : 0 < d) : Kith s (stopper X E a d) (fun n=>stopper (Z n) E a d):=by
    unfold stopper
    by_cases ha:a≤E
    · simp only [if_pos ha];exact kith_ebb (purchased a ha d hd) (min_le_right ..)
    simp only [if_neg ha]
    exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
  refine ⟨s,positive,_,B0,geom,?_⟩
  intro i a ha d hd
  have v:= kith_swim (landing_row q (Row.rights _ _ (rayStrip P L h B0 geom) positive.le)) _ positive
    (.of_forall (ray_grated P L h positive.le B0 geom)) (ray_flip P L h) dots i a d hd
  rw [through_swim (lands q) (stopper X E) X i E (fun j hj=>if_pos hj) a ha] at v
  have edge(n : Side) : swim (q.acts n) (stopper (Z n) E) i a=swim (q.acts n) (Z n) i a:=
    through_swim _ _ _ i E (fun j hj=>if_pos hj) a ha
  change Kith s (swim (lands q) X i a d) (fun n=>swim (q.acts n) (Z n) i a d)
  simpa only [edge] using v

end YM.Integration.WilsonConditionalTaylorMarkedWaves
end

