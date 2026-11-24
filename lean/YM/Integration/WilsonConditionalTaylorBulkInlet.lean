import YM.Integration.WilsonConditionalTaylorBulkRows

/-! Change the incoming finite field in the original Wilson/Haar primitive.
The same normalized noise and chart terms are paid by their original bounds;
only the genuine, regrouped old spatial polynomial requires a prior limit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkInlet
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open WilsonConditionalTaylorBulkRows
open scoped Topology BigOperators Classical

variable {G : Gauge} {n f : Side}

theorem tensor (S : StepData n f) (L : Lodge S.patch) (ρ : ChartRatio G) (k : S.Choices)
    (hK : S.patch.Branches S.kernel G) (hr : LocalRatio ρ) (U : Pap (wire G f)) (e d : ℕ) (i : Fin d) :
    rancho (joust (saddleP G S L) (flush L.forest k ρ U)) e d =
      pearl ((pane G S.patch L).acts n) (pearl ((winging (Rim G S.patch) (Loc G 1)).acts n)
        (rancho (joust (unitSplit G S 1) U) e d) - cum i n (TO G S.patch S.kernel e d)) + cum i n (WO S.patch L ρ e d) := by
  have raw : rancho (joust (staging G S) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom U)) e d =
      pearl ((winging (Rim G S.patch) (Loc G 1)).acts n) (rancho (joust (unitSplit G S 1) U) e d) :=by
    rw [Bank.yarn]
    unfold rancho
    rw [coeff_map];exact Lava.target ..
  rw [mirror_in,WO_tor G S ρ L hr,TO_tor G S k hK,←raw]
  unfold rancho
  rw [map_add,marble_add,coeff_map]
  congr 1
  change marble d (mixRows _ _)=_
  rw [Lava.target,map_sub];simp_rw [←canyon_eq,map_sub]

variable {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (ρ : ChartRatio G)
    (h : P.patch.Branches K G)

theorem moved (n : Side) (k : (primary P.patch K n).Choices) (U : Pap (wire G (n*P.L))) (e r : ℕ)
    {s C : ℝ} (hs : 0 < s) (hc : 0 ≤ C) (he : (P.duo K.penalty).A0.strip s C) :
    rancho (inlet P L ρ h n k U) e r = if e=0 then 0 else pearl ((zealand K P L G).acts n)
      (rancho (joust (saddleP G (primary P.patch K n) L) (flush (Reef.floor K P L n) k ρ U)) e r) :=by
  by_cases hx:e=0
  · subst e;unfold rancho inlet joust;rw [coeff_map,cobalt_base,map_zero,marble_zero,if_pos rfl]
  unfold rancho inlet
  rw [if_neg hx,cobalt,show joust _ (_-_) = joust _ _-joust _ _ from map_sub (PowerSeries.map _) _ _,map_sub,
    show joust (saddleP _ _ _) (.C _) = _ from PowerSeries.map_C _ _,PowerSeries.coeff_C,if_neg hx,sub_zero]
  rw [shifted P L h n _ s C hs hc he,coeff_map];exact Lava.target ..

variable (k : ∀ n, (primary P.patch K n).Choices) (U : (n : Side)→Pap (wire G (n*P.L))) (W : Pot G)

/-- This comparison starts before adding Haar and noise and before changing
the saddle mean. It ends with the full original shifted interaction. -/
theorem sourced (hr : LocalRatio ρ) (room : 4 ≤ t) (e r : ℕ) (i : Fin r) {w : ℝ} (positive : 0 < w)
    (old : Kith w (altitude P.patch W e r) (fun n=>rancho (joust (unitSplit G (primary P.patch K n) 1) (U n)) e r)) :
    ∃ s : ℝ, 0 < s ∧ Kith s (cola W ρ P L K e r) (fun n=>rancho (inlet P L ρ h n (k n) (U n)) e r) :=by
  obtain ⟨γ,C,hγ,hC,base⟩:=aone P (K:=K) G room
  let s:=min γ w
  have hs:0 < s:=lt_min hγ positive
  have he := strip_mono base (min_le_left γ w) (le_refl C)
  refine ⟨s,hs,?_⟩
  unfold cola
  simp_rw [moved P L ρ h _ _ _ e r hs hC he]
  by_cases zero:e=0
  · simp only [zero,↓reduceIte];exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
  simp only [zero,↓reduceIte]
  have field n:=tensor (primary P.patch K n) L ρ (k n) h hr (U n) e r i
  simp_rw [field];clear field
  unfold primary
  let X:=locating G K P L
  obtain ⟨A,hA,geo⟩:=Lodge.bothPay G K L _ hs
  have hX:X.strip s (A*C):=(geo _ _ hC he).1
  apply water_pearl (zealandPay K P L hX) _ i hs (le_trans zero_le_one (le_max_left ..))
  unfold ouzo Bank.atlas
  obtain ⟨B,hB⟩:=TO_bail G e r s P.patch K
  obtain ⟨H,hH⟩:=WO_bail G e r s L ρ
  have inlet:=water_pearl (M:=winging (Rim G P.patch) (Loc G 1)) (wing_strip _) (kith_ebb old (min_le_right γ w)) i hs zero_le_one
  exact (water_pearl (pane_pay L s) (kith_minus inlet (stable hs.le (TO_up G P.patch K e r) hB i)) i hs zero_le_one).add
    (stable hs.le (WO_up G L ρ e r) hH i)

end YM.Integration.WilsonConditionalTaylorBulkInlet
end

