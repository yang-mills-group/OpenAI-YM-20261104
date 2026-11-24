import YM.Integration.WilsonConditionalTaylorMarkedPass

/-! The separately computed finite torus predecessor stone also funds the
same whole signed covering transfer, including arbitrary changing occupied
rows. This is the unreset transfer used by the independently stored trees. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorIndependentMarked
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open scoped Topology BigOperators Classical

theorem rank {G : Gauge} (W : Pot G) (hp : Vivid W) (n : Side) : WilsonConditionalTaylorBulkShape.Ranks (stone W n) :=by
  intro e r _ active
  cases r with
  | zero =>
    have empty : rancho (stone W n) e 0=0 := (marble_eq_zero_iff _ _).mpr (by
      rw [sow_coeff,sow,map_sum]
      exact Finset.sum_eq_zero fun l _=>MvPolynomial.homogeneousComponent_of_mem (facade_grade _ _)|>.trans (if_neg (by omega)))
    exact (active empty).elim
  | succ r =>
    have live : W e (r+1)≠0:=by
      intro zero;apply active;rw [hp.flower e _ 0 n,zero,cum_zero]
    exact (hp.valence e (r+1) live).2

theorem all {G : Gauge} {K : KernelChoices} {j t l : ℕ} (P : Flight j t) (L : Lodge P.patch) (W Z : Pot G)
    (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : ∀ n, (primary P.patch K n).Choices)
    (V : (n : Side)→Pap (wire G n)) (original : Story W (pink K.penalty P.wing)) (hr : LocalRatio ρ)
    (room : 4≤t) (e d u : ℕ) (hu:l≤u) (sky : Young Z l) (tori : ∀ n,Young (rancho (V n)) l)
    (x : edgeL G) (y : Loc G 1)
    (source : ∀ a ≤ e, ∀ r ≤ l+e,∃ s:ℝ,0<s ∧ Kalm s x (Z a r) (fun n=>rancho (V n) a r)) :
    ∃ s:ℝ,0<s ∧ Kalm s (chief P x y) (braise P L W Z ρ h u e d)
      (fun n=>rancho (Reef.tossed P ρ h L n (k n) (stone W (n*P.L)) (V (n*P.L))) e d) :=by
  obtain ⟨v,C,hv,hC,H,_⟩:=colors G K.penalty K.penalty_pos P.legal
  apply WilsonConditionalTaylorMarkedPass.full P L W Z ρ h k (stone W) V original.toVivid hr room e d u hu
  · exact stoned_main hv.le hC.le (H P.wing).1 original.toVivid original.ink
  · exact rank W original.toVivid
  · exact sky
  · exact tori
  · intro a _ r positive _
    let i:Fin r:=⟨0,positive⟩
    obtain ⟨s,B,pos,due⟩:=original.fare a r
    refine ⟨s,pos,?_⟩
    simp only [original.toVivid.flower a r i]
    exact stable pos.le (original.civil a r) due i
  exact source

end YM.Integration.WilsonConditionalTaylorIndependentMarked
end

