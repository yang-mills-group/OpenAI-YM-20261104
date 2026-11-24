import YM.Integration.WilsonConditionalTaylorMarkedRetile

/-! Exact real finite chart pullback and its rooted spatial weight for a
general signed source, including joint sources and its scalar field row. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedInlet
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (h : P.patch.Branches K G)

def bank (n : Side) (Z : Pap (wire G (n*P.L))) := joust (saddleP G (primary P.patch K n) L)
  (lever (ferry P h L n) (Reef.seat (Reef.floor K P L n) Z))

theorem rows (n : Side) (Z : Pap (wire G (n*P.L))) (e r : ℕ) {w A : ℝ} (pos : 0<w) (fee : 0≤A)
    (kernel : (P.duo K.penalty).A0.strip w A) :
    rancho (bank P L h n Z) e r = pearl ((zealand K P L G).acts n) (pearl ((pane G P.patch L).acts n)
      (pearl ((winging (Rim G P.patch) (Loc G 1)).acts n) (jetty (splitCo (endo n P.L) (Loc G 1)).symm (rancho Z e r)))) :=by
  unfold bank
  rw [shifted P L h n _ w A pos fee kernel]
  exact (rename_income _ _ e r).trans (congrArg (pearl _) (tor_yolk (primary P.patch K n) L Z e r))

theorem sourced (room : 4 ≤ t) (Z : Pot G) (V : (n:Side)→Pap (wire G n)) (x : edgeL G) (y : Loc G 1)
    (e r : ℕ) {w : ℝ} (positive : 0<w) (prior : Kalm w x (Z e r) (fun n=>rancho (V n) e r)) :
    ∃ s : ℝ, 0<s ∧ Kalm s (coastRight _ _ _ (chief P x y)) (coves K P L Z e r)
      (fun n=>rancho (bank P L h n (V (n*P.L))) e r) :=by
  obtain ⟨γ,C,hγ,hC,base⟩:=aone P (K:=K) G room
  let s:=min γ w
  have hs:0<s:=lt_min hγ positive
  have he:=strip_mono base (min_le_left γ w) (le_refl C)
  refine ⟨s,hs,?_⟩
  simp_rw [rows P L h _ _ e r hs hC he]
  unfold coves Glide.urn
  obtain ⟨A,hA,geo⟩:=Lodge.bothPay G K L s hs
  have hX:(locating G K P L).strip s (A*C):=(geo _ _ hC he).1
  have B:1 ≤ (P.L.val:ℝ):=by exact_mod_cast P.L.property
  have bill:=WilsonConditionalTaylorMarkedRetile.scaled (τ:=s) P.L (le_trans (min_le_right γ w)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr B) positive.le])) positive.le hs.le x prior
  have wing:=kalm_stream (R:=winging (Rim G P.patch) (Loc G 1)) (Sum.inr y) (wing_strip s) zero_le_one hs bill
  have pane':=kalm_stream (R:=pane G P.patch L) (Sum.inr y) (pane_pay L s) zero_le_one hs wing
  have last:=kalm_stream (R:=zealand K P L G) (Sum.inr y) (zealandPay K P L hX) (le_trans zero_le_one (le_max_left ..)) hs pane'
  unfold chief coastRight;exact last

end YM.Integration.WilsonConditionalTaylorMarkedInlet
end

