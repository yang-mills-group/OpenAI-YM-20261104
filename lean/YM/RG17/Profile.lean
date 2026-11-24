import YM.RG17.Balance

/-!
# Single cluster (ordinary OPE finite truncation), smooth joint profiles

Origin 0, Euclidean measure and normalized positions (including arguments
not reflection ordered). Profiles supported in a fixed compact K of
Conf. The integrals below are of the actual COMPLETE correlations / packet
with the unit term and all lower-grade fields in it. `Demand` allows
bookkeeping of uniform higher derivative and support prices in the report
stage; here even L¹ suffices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (L:Layout F)
variable {n:ℕ}

structure Demand (j:ℕ)(ψ:Test n)(b:ℝ) : Prop where
    nonneg : 0 ≤ b
    norm : (∫ x : Points n, ‖ψ x‖) ≤ b
    smooth (l:ℕ) : l≤j → ∀ x:Points n, ‖iteratedFDeriv ℝ l (ψ : Points n→ℂ) x‖ ≤ b
set_option maxHeartbeats 800000 in
lemma demandAccessible (j:ℕ)(ψ:Test n):∃ b,Demand j ψ b:=by
   have hf (l:ℕ):∃ b:ℝ,∀ x: Points n, ‖iteratedFDeriv ℝ l (ψ:Points n→ℂ) x‖≤ b := by
     have H : ContDiff ℝ ∞ (ψ : Points n → ℂ) := ψ.contDiff
     have ht : Continuous (fun x => (iteratedFDeriv ℝ l (ψ : Points n → ℂ) x)) := H.continuous_iteratedFDeriv (m:=l) (WithTop.coe_le_coe.mpr le_top)
     have hh : HasCompactSupport (iteratedFDeriv ℝ l (ψ:Points n→ℂ)) := HasCompactSupport.iteratedFDeriv (𝕜:=ℝ) (f:= (ψ:Points n→ℂ)) ψ.hasCompactSupport l
     exact Continuous.bounded_above_of_compact_support (f:=iteratedFDeriv ℝ l (ψ:Points n→ℂ)) ht hh
   choose b hb using hf
   obtain ⟨B,hB,h₀,hc⟩:=((eventually_all.mpr (fun i : Fin (j+1)=> eventually_ge_atTop (b i))).and
        ((eventually_ge_atTop 0).and (eventually_ge_atTop (∫ x:Points n,‖ψ x‖)))).exists
   exact ⟨B,h₀,hc,fun l hl x=> (hb ..).trans (hB (⟨l,Nat.lt_succ_of_le hl⟩:Fin (j+1)))⟩
lemma Demand.fewer {j k:ℕ}{ψ:Test n}{b:ℝ}(h:Demand j ψ b)(hk:k ≤ j):Demand k ψ b :=
    ⟨h.nonneg,h.norm,fun l hl x=>h.smooth l (hl.trans hk) x⟩

section zoom
def posed (r:ℝ)(x:Points n) := fun i:Fin n=> r • x i
lemma roomCosts {K:Set (Points n)}(h:IsCompact K)(hk:K⊆conf _) : ∃ T η:ℝ, 0≤T ∧ 0<η ∧
    ∀ r:ℝ, 0<r → ∀ x∈ K, WithinRoom r T η (posed r x) 0 := by
   obtain e|he:= K.eq_empty_or_nonempty
   · exact ⟨0,1,le_rfl,zero_lt_one,by simp [e]⟩
   obtain ⟨B,hB⟩:= h.exists_bound_of_continuousOn (f:=id) continuousOn_id
   have hf (i j:Fin n) (hb:i≠j) : ∃ u:ℝ, 0<u ∧ ∀ x∈K,u ≤ ‖x i-x j‖:=by
      obtain ⟨x,hx,hi⟩:= h.exists_isMinOn (f:=fun x=> ‖x i-x j‖) he (Continuous.continuousOn (by fun_prop))
      exact ⟨_, norm_sub_pos_iff.mpr ((hk hx).ne hb), hi⟩
   have hf' : ∀ i j:Fin n,∀ᶠ u in home,i≠j → ∀ x∈K,u ≤ ‖x i-x j‖:=by
      intro i j; by_cases h:i=j
      · exact Eventually.of_forall fun _ H=> False.elim (H h)
      obtain ⟨u,hu,he⟩:= hf i j h
      filter_upwards [(show ∀ᶠ z in (𝓝[>] (0:ℝ)),z ≤ u from nhdsWithin_le_nhds (ge_mem_nhds hu))] with z hz _ x hx using hz.trans (he x hx)
   obtain ⟨u,hu,hU⟩:= (positiveLength.and (eventually_all.mpr (fun i=>eventually_all.mpr (hf' i)))).exists
   refine ⟨max B 0,u,le_max_right ..,hu,fun r hr x hx=>⟨fun i=>?_,fun i j hi=>?_⟩⟩
   · unfold posed; rw [sub_zero,norm_smul_of_nonneg hr.le,mul_comm]
     exact mul_le_mul_of_nonneg_right (((PiLp.norm_apply_le x i).trans (hB x hx)).trans (le_max_left B 0)) hr.le
   unfold posed; rw [← smul_sub,norm_smul_of_nonneg hr.le,mul_comm]; exact mul_le_mul_of_nonneg_left (hU i j hi x hx) hr.le
end zoom

lemma localized {E:Type*} [NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E]
    (ψ:Test n) (g:Points n→E) (hx:∀x∈tsupport ψ,ContinuousAt g x) : Integrable (fun x=>ψ x • g x) := by
    have h:Continuous (fun x=>ψ x • g x):=by
       apply continuous_iff_continuousAt.mpr; intro x; by_cases he:x∈tsupport ψ
       · exact ψ.continuous.continuousAt.smul (hx x he)
       apply ContinuousAt.congr (f:=fun _ : Points n=> (0:E)) continuousAt_const
       filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈ (tsupport ψ)ᶜ from he)] with i hi
       rw [image_eq_zero_of_notMem_tsupport hi,zero_smul]
    exact h.integrable_of_hasCompactSupport ψ.hasCompactSupport.smul_right

-- Choose measurement origin = 0.
variable {J:Type} [Fintype J] {d:Fin n→ℕ} {v:ℝ→ Labels S d} {e:J→ℕ}
def query (F:Final C f S)(v:Labels S d)(y:J→ E4)(w:Labels S e)(view:Viewers F)
     (r:ℝ)(ψ:Test n):ℂ := ψ.applyTo (fun x=>whole (spectator F view) (posed r x) v y w)
def basket (d':ℕ) (v:Labels S d)(r:ℝ) (ψ:Test n) := ∫ x: Points n, ψ x • P.packet d' (posed r x) v 0

def stems (L:Layout F) (slots:(i:Fin n)→ Slot C (d i)) (r:ℝ):Labels S d:=fun i=> input L r (d i) (slots i)

lemma posed_continuous (r:ℝ) : Continuous (posed (n:=n) r) :=by
   unfold posed; apply continuous_pi; intros; fun_prop

lemma basket_int (v:Labels S d) {r:ℝ} (D:ℕ) (ψ:Test n)
   (h:∀ x∈tsupport ψ, ∀ k≤D,orbitMargin P.port k (posed r x) 0):
   Integrable fun x : Points n=> ψ x • P.packet D (posed r x) v 0 := by
    apply localized; intro x hx
    unfold Reader.packet
    apply ContDiffAt.continuousAt (𝕜:=ℝ) (n:=∞); apply ContDiffAt.sum; intro i _
    let fi:ℕ:= (i:Fin (D+1)).val; have he:fi ≤D:= Nat.le_of_lt_succ i.isLt
    apply (((F.sector.derivatives.rise he).toContinuousLinearMap).restrictScalars ℝ).contDiff.contDiffAt.comp (𝕜:=ℝ)
    refine ContDiffAt.comp (g:=fun z:(Fin n→E4) × E4=> P.fresh fi z.1 z.2 v) (f:=fun x:Points n=>(posed r x,(0:E4))) x
       (P.fresh_smooth fi _ _ v (h x hx fi he)) ?_
    refine ContDiffAt.prodMk ?_ contDiffAt_const
    unfold posed; apply contDiffAt_pi.mpr; intro i; fun_prop

variable (h:Services C f S)
include P h
lemma testedPacketBound (v:ℝ→Labels S d) (D:ℕ)(c:Fin n→ℝ)(z:GradePrice P d v c) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)
    {ε δ:ℝ}(hp:0<ε)(hδ:0<δ)(w:Labels S e) :
    ∀ᶠ r in home,∀ ψ:Test n, tsupport ψ ⊆ K → ∀ (y:J→ E4), ClearOf 0 y δ →
      ∀ view:Viewers F,
        ‖query F (v r) y w view r ψ - (upon (spectator F view) D 0 y w) (basket P D (v r) r ψ)‖≤
          r^((D+1:ℝ) - (∑ i,c i) - ε)*(∫ x:Points n,‖ψ x‖):=by
    obtain ⟨T,η,hT,hη,hx⟩:= roomCosts hK hx
    have he:= formulaCharged P h hT hη w D z hδ hp
    have hd:= (profile_scope (ε:=ε) F P h (v 1) w hT hη hδ hp D)
    filter_upwards [he,positiveLength,hd] with r hr hz hd ψ hψ y hy view
    let a := r^((D+1:ℝ)-(∑ i,c i)-ε)
    have ha:0≤a:= Real.rpow_nonneg hz.le _
    let W:= spectator F view
    have hs (x) (h:x∈tsupport ψ): ((posed r x,(0:E4),y):Loc (Fin n) J) ∈guardZone F P D:=
       (hd.2 _ (Set.mem_setOf.mpr ⟨hx r hz x (hψ h),hy⟩)).1
    have hi : Integrable (fun x=>ψ x*whole W (posed r x) (v r) y w) := by
        refine localized ψ _ (fun x hv=> ?_ )
        exact (whole_cont_at (v r) w _ (spectate F view) ((hs x hv).2.1)).comp (f:=fun x:Points n=> ((posed r x,(0:E4),y):Loc (Fin n) J))
          (((posed_continuous r).prodMk continuous_const).continuousAt)
    let f: S.Field D→L[ℂ] ℂ:= LinearMap.toContinuousLinearMap (upon W D 0 y w)
    let g:= fun x:Points n=> ψ x • P.packet D (posed r x) (v r) 0
    have hg: Integrable g := basket_int P _ D ψ (fun i hi j hj=> (hs i hi).1 _ hj)
    change ‖(∫ x:Points n,ψ x*whole W (posed r x) (v r) y w) - f (∫ x: Points n,g x)‖≤ _
    rw [← f.integral_comp_comm hg,← MeasureTheory.integral_sub hi (f.integrable_comp hg)]
    refine (norm_integral_le_of_norm_le (g:=fun x:Points n=> a*‖ψ x‖) ?_ ?_).trans_eq (integral_const_mul ..)
    · exact ((ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm).const_mul _
    apply Eventually.of_forall; intro x
    by_cases he:x∈ tsupport ψ; swap
    · simp [image_eq_zero_of_notMem_tsupport he,g]
    change ‖ψ x* _ - f (g x)‖ ≤ _
    unfold g
    rw [map_smul,smul_eq_mul,← mul_sub,norm_mul,mul_comm ‖ψ x‖]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    change ‖_ - upon W D (0:E4) y w (P.packet D (posed r x) (v r) 0)‖≤ _
    rw [packet_read F P _ _ _ _ _ view D ((hs x he).2.2)]
    exact hr _ _ _ (hx r hz x (hψ he)) hy view

lemma testedPacketLocated (loc:Located L) (v:(i:Fin n)→Slot C (d i)) (D:ℕ) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)
    {ε δ:ℝ}(hp:0<ε)(hδ:0<δ)(w:Labels S e) :
    ∀ᶠ r in home,∀ ψ:Test n, tsupport ψ ⊆ K → ∀ (y:J→ E4), ClearOf 0 y δ →
      ∀ view:Viewers F,
        ‖query F (stems L v r) y w view r ψ - (upon (spectator F view) D 0 y w) (basket P D (stems L v r) r ψ)‖≤
          r^((D+1:ℝ) - ε)*(∫ x:Points n,‖ψ x‖):=by
   have hz:GradePrice P d (stems L v) (fun _=>0):=by
       intro i j; rw [add_zero]; exact inputUpper P L h loc _ _ _
   simpa only [Finset.sum_const_zero,sub_zero] using (testedPacketBound P h (stems L v) D (fun _=>0) hz hK hx hp hδ w)

end YM.RG17
