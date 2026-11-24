import YM.FormalBulk08.Kemp.Vibes

/-! Qualitative step keeps earned per-grade width. Auth only, not
purchasing moving constants. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree Work.F08
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B C : ℝ} {l i u j t r D d : ℕ}{K: KernelChoices}
variable (a:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(Y: Anthem D G)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
    (hp: Wade a Y l)(hv: Story W (pink K.penalty P.wing))(hr: LocalRatio ρ)(hL:2≤P.L.val)
    (ht:4≤t)(hu:l≤u)(k:(n:Side)→ (primary P.patch K n).Choices)

include hp hv hr ht hu
lemma brig (e r d:ℕ): ∃ η:ℝ,0<η ∧ (∀ p, Kalm η (0,a) (quick P V W Y ρ h hL d u p e r) (fun n=>rancho (quickP P V W Y ρ h hL d u p n (k n)) e r)) ∧ LightPay (fame _) η (0,a) (fun p=>quick P V W Y ρ h hL d u p e r) (‖·‖):= by
    obtain ⟨θ,hθ,hf,hU⟩:= wedge_step a P Y W hp hv hL e; obtain ⟨s,C,hs,hC,hA⟩:=aone P (K:=K) G ht
    obtain ⟨z,B,hz,hB⟩:=(gamma_ready G K P V h).1
    let η:=min (min s z) (P.L.val * θ); have hη : 0<η:=by unfold η; positivity
    have hT:= show (Flight.duo K.penalty P).A0.strip η C from strip_mono hA ((min_le_left ..).trans (min_le_left ..)) le_rfl; let c:ℝ:=max 0 B; have hc:0≤c:=le_max_left ..
    let q:=lands (rayshot P V h);have Q : (gamma G K P V h).strip η c:= strip_mono hB ((min_le_left ..).trans (min_le_right ..)) (le_max_right ..)
    have hh : η≤P.L.val *θ:= min_le_right ..
    let X := coastRight Cover (Minor G P.patch V) (Loc G 1) (0,a)
    obtain ⟨H,hS⟩:=ray_cover P V h hη.le hc Q
    refine ⟨η,hη,fun p=>?_,?_⟩
    · unfold quick; simp_rw [quick_income P V W,Pi.smul_apply, Finset.sum_apply, braise]; have he x n:=truss_rite P V W (stepsong P Y hL p x) ρ h hv hr ht (step_can a P Y hp hL p x) _ (step_agate a P Y hp hL p x) hu e r n (k n); simp_rw [he]; apply Kalm.smul; apply kalm_many _; intro x _; apply kalm_many _;intro i _; apply kalm_cut;have hx:=budding P V W (stepsong P Y hL p x) ρ h hv hr (step_can a P Y hp hL p x) (step_agate a P Y hp hL p x) hu k i e r hη hC hT hh hc Q (lift x,a) a hf (fun i hi m=>by obtain ⟨B,-,hB⟩:=hU i hi m;exact ⟨_,hB p x⟩)
      rwa [chief_h a P x] at hx
    unfold quick; simp_rw [Pi.smul_apply,Finset.sum_apply, braise];apply LightPay.amp;apply pay_sums;intro x _;apply pay_sums; intro i hi
    have H': LightPay (fame _) η X (fun p=>border P V W (stepsong P Y hL p x) ρ h i e r) (‖·‖):= by
       refine light_income (o:=X) e i q (magma P V W ρ h) (fun p=> coves K P V (stepsong P Y hL p x)) hη.le (H.turn hS) (fun i b _ hb r l=>?_) (fun j hj r=>?_ ) e le_rfl r
       · obtain ⟨hp,C,H⟩:= redskin P V W ρ h k hη hC hh hT hc Q hv.toVivid hr i b r (⟨0,l⟩:Fin r) (fun j hj r=> hf j (hj.trans hb) r); exact ⟨C,lit_width hp C H⟩
       obtain ⟨B,hB,H⟩:=hU j hj r
       let W:=scroll P.patch.L (Loc G 1) (lift x,a)
       obtain ⟨A,hA,hv⟩:= Lodge.bothPay G K V η hη
       have hM:(locating G K P V).strip η (A*C):=(hv _ _ hC hT).1
       let d:=Fintype.card (Board G P.patch); let D':=Fintype.card (BoardL G P.patch V);
       let g:ℝ:=max 1 (A*C); have hg:0≤g:=le_trans zero_le_one (le_max_left ..)
       let u:ℝ:=Real.exp (8*η)*B*(d:ℝ)^r*(D':ℝ)^r*((D':ℝ)*g)^r; refine ⟨u,by unfold u; positivity,fun p=>?_⟩
       have hx:=H p x; have hZ : Knoxville (fame _) θ ((scroll P.patch.L (Loc G 1)).symm W) _ _:= (scroll P.patch.L (Loc G 1)).symm_apply_apply (lift x,a) |>.symm ▸ hx
       have hh:=rinse_bill _ _ hh hη.le _ hZ
       have he:=penn_pearl (winging (Bank.Rim G P.patch) (Loc G 1)) _ (Sum.inr a) hh hη.le (wing_strip η) zero_le_one
       have hz:=penn_pearl (pane G P.patch V) _ (Sum.inr a) he hη.le (pane_pay V _) zero_le_one
       have hy:=penn_pearl (zealand K P V G) _ (Sum.inr a) hz hη.le (zealandPay K P V hM) hg
       unfold X; rw [←chief_h a P x]; apply Knoxville.mono hy; apply le_of_eq; unfold u; change 1*(1*(1*(_*((d:ℝ)*1)^r)*((D':ℝ)*1)^r)*((D':ℝ)*g)^r)=_; ring
    obtain ⟨R,hR,U⟩:=H'; exact ⟨R,hR,fun p=>penn_port (U p)⟩

lemma quick_Wade (d:ℕ) : Wade a (quick P V W Y ρ h hL d u) l:=by
    let k n:= Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n))
    have hh:=brig a P V Y W ρ h hp hv hr hL ht hu k
    refine ⟨fun p=> quick_yield _ _ _ _ _ _ _ hL hp hv.toVivid hr p,fun p e r=> ?_,fun e r=> ?_⟩
    · obtain ⟨s,-,H,-⟩:=hh e r d; exact light_agate (H p).1 (.of_forall fun _=> marble_agate _ _)
    obtain ⟨s,hs,-,C,hC,H⟩:=hh e r d; exact ⟨s,C,hs,hC,H⟩
end YM.FormalBulk08.Kemp
