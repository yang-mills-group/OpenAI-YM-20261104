import YM.FormalBulk08.Bank.Wet

/-! Valence survives also r=0 on torus simulants, needed for truncation.
Log series positive, includes scalar terms. Don't export quantity at infinite
volume on those. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {U V : Type*} [Fintype U] [Fintype V]

lemma quake (u : Pap U) (P : U≃V) (e r) : (rancho u e r=0)↔ rancho (joust P u) e r=0 := ⟨fun h=>by rw [joust_level,h,jetty_zero],fun h=>by rw [infer_joust P,h,jetty_zero]⟩
lemma vacant (P : U→V) (u : Pap U) (e r) (h : rancho u e r=0) : rancho (PowerSeries.map (MvPolynomial.rename P).toRingHom u) e r=0 := by
   unfold rancho; rw [coeff_map]; change marble r (MvPolynomial.rename P _)=_; rw [Shore.pebble,show marble _ _=0 from h];funext; simp [cores]
lemma match_cap (M : U→V→ℝ) (p : Pap U) (e r)(h:rancho p e r=0): rancho (PowerSeries.map (mixRows M).toRingHom p) e r=0:= by unfold rancho; rw [coeff_map];change marble _ (mixRows M _)= _; rw [Lava.target,show marble _ _=0 from h,pearl_zero]
variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (T : Lodge P.patch) (L : Pot G) (ρ : ChartRatio G)
lemma fiat {s b : ℝ} (h : P.patch.Branches K G) (n : Side) (k : (primary P.patch K n).Choices) (hp : Vivid L) (ht : LocalRatio ρ) (hs : 0<s) (hb : 0≤b) (hu : (Flight.duo K.penalty P).A0.strip s b) : Fiery (rancho (coffer L ρ P T h n k)) := by
   intro e r he; rw [posted L ρ P T h n k e r hs hb hu] at he; split at he
   · contradiction
   rename_i hE;by_contra! hx
   let S:= primary P.patch K n;let U:=Mesa.stone L (n*P.patch.L);let F:=Reef.floor K P T n; let H:= joust (saddleP G S T)
   have hg : 0<e:=Nat.pos_of_ne_zero hE
   have hw : rancho U e r=0:= by
      rcases r with (_|r)
      · unfold U rancho; rw [marble_eq_zero_iff,sow_coeff,sow,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade _ _),if_neg (by omega)]
      unfold U;rw [hp.flower _ (r+1) 0]; have hL : L e (r+1)=0:= by by_contra H; have ha:=hp.valence _ _ H;omega
      rw [hL,cum_zero]
   let Z:= (noisePin S k (G:=G)); have hz : rancho Z e r=0 := by
       unfold Z noisePin rancho;rw [after_one,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (by omega)]
   have h₁ : rancho (H (halo (sap F ρ) (wire G n))) e r=0:= by
       apply (quake _ _ _ r).mp; apply vacant
       have hv:= sap_root F ρ ht; unfold rancho; rw [marble_eq_zero_iff, MvPolynomial.homogeneousComponent_of_mem (log_grade (p:=paste (sap F ρ)) (by rw [paste_first,hv,map_one]) (paste_grade (sap F ρ)) e),if_neg (by omega)]
   have hR : rancho (H (flush F k ρ U)) e r=0 := by
       unfold H;rw [mirror_in ρ S T k U]; unfold rancho;rw [map_add,marble_add,show marble _ _=0 from h₁,add_zero];apply match_cap
       unfold rancho; rw [map_sub,←canyon_eq,map_sub];simp_rw [canyon_eq]; rw [show marble _ _=0 from (quake _ _ _ _).mp (vacant _ U _ _ hw), show marble _ _=0 from (quake _ (staging G S) _ _).mp hz,sub_zero]
   exact he (by rw [show rancho _ _ _= _ from hR,pearl_zero])
-- choose Uniform tags for default acts/winding (ANY okay)
lemma bath_vac {s b:ℝ} (h : P.patch.Branches K G) (n : Side) (k : (primary P.patch K n).Choices) (hp : Vivid L) (ht : LocalRatio ρ) (hs : 0<s) (hb : 0 ≤ b) (hu : (Flight.duo K.penalty P).A0.strip s b) : Fiery (fun e r=> marble r (coeff e (cobalt (ferry P h T n) (flush (Reef.floor K P T n) k ρ (stone L (n*P.patch.L)))))) := fun e r he=> fiat P T L ρ h n k hp ht hs hb hu e r fun hz=>he ((quake _ _ _ _).mpr hz)
end YM.FormalBulk08.Bank
