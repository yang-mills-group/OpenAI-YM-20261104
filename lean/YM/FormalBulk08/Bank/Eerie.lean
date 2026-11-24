import YM.FormalBulk08.Bank.Glass

/-! Existential width for legitimacy of cover computation. NOT used to
iterate a price. From Ward passage and Kith deduce Civic of periodized output.
Quantitative rates for it later, for now per tensor. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {V I : Type*} {J : Type*} {η : ℝ}

-- Fatou
lemma lit_width {r : ℕ} {T : Tile (Biglot I) r} {P : (n:Side)→Tile (Tor n I) r} (h : Light T P) (C : ℝ) (H : Bright P η C) : Bail (fame _) η T C := by
   have hc:=H.exists.choose_spec.1
   refine ⟨hc,fun i a=>?_⟩
   have hv (v : chain (Biglot I) r): ∀ᶠ n in atTop, wide (lake n I) (Lotus.drip n ∘ v)=wide (fame I) v := by
      have he (x y: Fin r) := effect ((v x).1-(v y).1)
      filter_upwards [eventually_all.mpr fun x=> eventually_all.mpr (he x)] with n hn; unfold wide; congr 1; ext ⟨x,y⟩; change size (lift (wrap n _-wrap n _))= size ((v x).1-(v y).1);rw [←map_sub,hn]
   rw [ENNReal.tsum_eq_iSup_sum,iSup_le_iff]; intro S
   let f (n) : Gorge.pack i a → Gorge.pack i (Lotus.drip n a) := fun v=> ⟨Lotus.drip n ∘ v.val, congr_arg (Lotus.drip n) v.property⟩
   have he : ∀ᶠ n in atTop,Set.InjOn (f n) S := by
      filter_upwards [S.eventually_all.mpr (fun (v:Gorge.pack i a) _=> eventually_all.mpr fun j=>boil_drip (v.val j))] with n hn t ht p hp e
      apply Subtype.ext; funext j; rw [←hn t ht j,←hn p hp j]; exact congr_arg _ (congr_fun (congr_arg Subtype.val e) j)
   have ht (v : Gorge.pack i a) : Tendsto (fun n=> glitter (lake n I) η (P n) (f n v).val) atTop (𝓝 (glitter (fame I) η T v.val)) := by
      have hg : Continuous (fun x:ℝ=> Gorge.shine η (wide (fame I) v.val)* ‖x‖ₑ):= by
         simp_rw [Gorge.shine,← ofReal_norm, ←ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)
      refine (hg.continuousAt.tendsto.comp (h v.val)).congr' ?_;filter_upwards [hv v.val] with n hn;change _= glitter _ η (P n) (Lotus.drip n ∘ v.val); unfold glitter;rw [hn]; rfl
   apply le_of_tendsto (tendsto_finsetSum _ (fun x _=>ht x)); filter_upwards [H,he] with n hn he
   rw [←Finset.sum_image (f:=fun v=>glitter (lake n I) η (P n) v.val) he]; exact (ENNReal.sum_le_tsum _).trans (hn.2 i _)
lemma boarded {r : ℕ} {T : Tile (Biglot (I⊕J)) r} {P : (n:Side)→ Tile (Tor n (I⊕J)) r} (h : Kith η T P) : Kith η (jetty (coastRight _ _ _) T) (fun n=>jetty (coastRight _ _ _) (P n)) := by
   obtain ⟨h,C,H⟩:=h; refine ⟨fun v=>?_ , C,H.mono (fun n hn=>?_)⟩
   · exact h _
   refine ⟨hn.1,fun i a=>?_⟩
   let g:= coastRight (Site n) I J; have hf : Injective g:= fun i j hw=> Prod.ext (congr_arg (fun v:Site n×(I ⊕ J)=>v.1) hw) (Sum.inr_injective (congr_arg Prod.snd hw))
   let t : Gorge.pack i a → Gorge.pack i (g a):=fun u=>⟨g ∘ u.val,congr_arg g u.property⟩
   have hu:=hn.watch t (fun u v h=>Subtype.ext (funext fun j=>hf (congr_fun (congr_arg Subtype.val h) j)))
   exact hu -- d definitional

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (T : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G) (h : P.patch.Branches K G)
lemma aone (G : Gauge) (ht : 4≤t): ∃ s C : ℝ,0 < s ∧ 0≤C ∧ (Flight.duo K.penalty P).A0.strip s C := by
   obtain ⟨s,C,hs,hC,H,-⟩:=transports G K.penalty K.penalty_pos P.legal ht; exact ⟨s,_,hs,by positivity,(H P [] (Nat.zero_le _)).1⟩
lemma ferried (hp : Story W (pink K.penalty P.wing)) (hr : LocalRatio ρ) (k : ∀ n, (primary P.patch K n).Choices) (ht : 4≤t) (e r i) (x:Fin r) :
     ∃ η : ℝ,0<η ∧ Kith η (magma P T W ρ h i e r) (fun n=> whirl P T W ρ h n (k n) i e r) := by
   obtain ⟨η,hη,H⟩:= demanded_finite P W hp e
   obtain ⟨s,C,hs,hc,hK⟩:=aone P (K:=K) G ht
   obtain ⟨z,B,hz,hB⟩:=(gamma_ready G K P T h).1
   let u:=min (min s z) (P.L.val*η); have hu:0<u:= by unfold u; positivity
   exact ⟨u,hu,redskin P T W ρ h k hu hc (min_le_right ..) (strip_mono hK ((min_le_left ..).trans (min_le_left ..)) le_rfl) (le_max_left 0 B) (strip_mono hB ((min_le_left ..).trans (min_le_right ..)) (le_max_right 0 B)) hp.toVivid hr i e r x H⟩
-- eventually shrink many in-place
lemma kith_ebb {r : ℕ} {T : Tile (Biglot I) r} {P : (n:Side)→Tile (Tor n I) r} {τ : ℝ} (H : Kith η T P) (he : τ≤η) : Kith τ T P:= ⟨H.1,H.2.choose,H.2.choose_spec.mono fun _ hn=> hn.shrink he⟩
lemma kith_joint {r : ℕ} {T : V → Tile (Biglot I) r} {U : V→(n:Side)→ Tile (Tor n I) r} (V : Finset V) (h : ∀ i∈V,∃ η : ℝ,0<η ∧ Kith η (T i) (U i)) : ∃ η : ℝ,0<η ∧ Kith η (∑ i∈V,T i) (fun n=>∑ i∈V,U i n) := by
   induction V using Finset.induction with
   | empty=>simp only [Finset.sum_empty];exact ⟨1,one_pos,fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
   | @insert i v he ih=> obtain ⟨s,hs,H⟩:=h i (Finset.mem_insert_self ..); obtain ⟨t,ht,hT⟩:=ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)); simp_rw [Finset.sum_insert he];exact ⟨min s t, lt_min hs ht,(kith_ebb H (min_le_left ..)).add (kith_ebb hT (min_le_right ..))⟩
lemma bank_skin (hp : Story W (pink K.penalty P.wing)) (hr : LocalRatio ρ) (k : ∀ n, (primary P.patch K n).Choices) (ht : 4≤t) (e r) (x: Fin r) : ∃ η : ℝ,0<η ∧ Kith η (coastRun P T W ρ h e r) (fun n=> whirled P T W ρ h n (k n) e r) := by
   unfold coastRun whirled; refine kith_joint _ fun i hi=>?_; obtain ⟨η,hη,H⟩:= ferried P T W ρ h hp hr k ht e r i x; exact ⟨η,hη,boarded H⟩
end YM.FormalBulk08.Bank
