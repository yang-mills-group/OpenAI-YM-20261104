import YM.FormalBulk08.Kemp.Where

/-! Root displacement exact; `any` positive moment budgets for first Ward
then larger paid costs later. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B C : ℝ} {l i u j t r : ℕ}

-- Fatou analogue
lemma vents_pay {Q : Tile (Biglot I) r}{P : (n:Side)→Tile (Tor n I) r}{o : Biglot I} (h:Light Q P)(H:Vent o P η A): Knoxville (fame _) η o Q A:= by
    refine ⟨H.exists.choose_spec.1,?_⟩
    rw [ENNReal.tsum_eq_iSup_sum,iSup_le_iff]; intro V
    have he(v:chain (Biglot I) r):∀ᶠ n in atTop,herb (lake n I) (Lotus.drip n o) (Lotus.drip n ∘ v)=herb (fame I) o v:= by
       let T:chain (Biglot I) (r+1):=Fin.cons o v
       filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>effect ((T i).1-(T j).1)))] with n hn; unfold herb wide; rw [←Fin.comp_cons]; congr 1; ext ⟨a,b⟩
       change size (lift (wrap n _-wrap n _))= size ((T a).1-(T b).1); rw [←map_sub, hn]
    have hr (v:chain (Biglot I) r): Tendsto (fun n=> penon (lake n I) (Lotus.drip n o) η (P n) (Lotus.drip n ∘ v)) atTop (𝓝 (penon (fame I) o η Q v)):= by
       let f z:= Gorge.shine η (herb (fame _) o v)*‖(z:ℝ)‖ₑ
       have hf: Continuous f := by unfold f Gorge.shine; simp_rw [← ofReal_norm, ←ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)
       refine (hf.continuousAt.tendsto.comp (h v)).congr' ?_; filter_upwards [he v] with n hn; unfold penon; rw [hn]; rfl
    apply le_of_tendsto (tendsto_finsetSum _ (fun i _=>hr i)); filter_upwards [H,V.eventually_all.mpr (fun v _=> eventually_all.mpr fun j=>boil_drip (v j))] with n hn hU
    rw [← Finset.sum_image (f:=fun v=>penon (lake n I) _ η (P n) v)]; swap;· intro i hi x hx ht; funext j; rw [← hU i hi j,← hU x hx j]; exact congr_arg _ (congr_fun ht j)
    exact (ENNReal.sum_le_tsum _).trans hn.2

variable {K : KernelChoices}(P:Flight j t)(V:Lodge P.patch)(W Z:Pot G)(ρ : ChartRatio G)
-- arbitrary shifts not collapsed to parent zero yet.
def chief (x: Biglot (Loc G 1)) (p: Loc G 1) : Biglot (Loc G 1):= ((scroll P.patch.L _ x).1,p)
lemma fresh_kernels (h:P.patch.Branches K G)(hZ:Young Z l)(hz:∀ e r,Agate (Z e r))(hu:l≤u) (hs:0<η)(ha:0≤A)(hv:(Flight.duo K.penalty P).A0.strip η A)
    (hη:η≤P.L.val*θ)(e r) (x:edgeL G)(y:Loc G 1)(H:Knoxville (fame _) θ x (Z e r) B):
    Kalm η (coastRight _ _ _ (chief P x y)) (coves K P V Z e r) (fun n=>rancho (sailors P V h Z u n) e r):= by
   simp_rw [fees_tor P V Z h hZ hz hu _ _ _ hs ha hv]; unfold coves Glide.urn;
   let W:= scroll P.patch.L (Loc G 1) x; obtain ⟨C,hC,hf⟩:= Lodge.bothPay G K V η hs
   have hX : (locating G K P V).strip η (C*A):=(hf _ _ ha hv).1
   have hz : Knoxville (fame _) θ ((scroll P.patch.L (Loc G 1)).symm W) (Z e r) B:=by unfold W; rw [Equiv.symm_apply_apply]; exact H
   have hu := sieve_kalm _ (rinse_bill (Z e r) P.patch.L hη hs.le W hz) hs.le
   have he:=kalm_stream (R:=winging (Bank.Rim G P.patch) (Loc G 1)) (Sum.inr y) (wing_strip η) zero_le_one hs hu
   have hy:=kalm_stream (R:=pane G P.patch V) (Sum.inr y) (pane_pay V η) zero_le_one hs he
   have hz := kalm_stream (R:=zealand K P V G) (Sum.inr y) (zealandPay K P V hX) (le_trans zero_le_one (le_max_left ..)) hs hy
   unfold altitude chief coastRight; exact hz
lemma budding (h:P.patch.Branches K G) (hp:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)(hZ:Young Z l)(hz:∀ e r, Agate (Z e r))(hf:l≤u)
    (k:∀ n, (primary P.patch K n).Choices)(n e r:ℕ)
    (hs:0<η)(ha:0≤A)(hv:(Flight.duo K.penalty P).A0.strip η A)(hη:η≤P.L.val*θ)(hB:0≤B)(hg:(gamma G K P V h).strip η B)(x:edgeL G)(y:Loc G 1)(H:∀ i≤e,∀ m,∃ A:ℝ, Bail (fame _) θ (W i m) A)(H':∀ i≤e,∀ m,∃ A:ℝ, Knoxville (fame _) θ x (Z i m) A):
    Kalm η (coastRight _ _ _ (chief P x y)) (border P V W Z ρ h n e r) (fun m=> calendarQ P V W Z ρ h u m (k m) n e r):= by
   refine kalm_group n e e r _ _ (fun n' d i hn hd hi=> ?_) (fun a m he=>?_ ) le_rfl (landing_row _ (Row.rights _ _ (rayStrip P V h hB hg) hs.le)) hs (.of_forall (ray_grated P V h hs.le hB hg)) (ray_flip P V h)
   · exact redskin P V W ρ h k hs ha hη hv hB hg hp.toVivid hr n' d i (⟨0,hi⟩ : Fin i) (fun i hi e'=> H i (hi.trans hd) e')
   obtain ⟨C,hC⟩:=H' a he m; exact fresh_kernels P V Z h hZ hz hf hs ha hv hη a m x y hC
end YM.FormalBulk08.Kemp
