import YM.SharpGram.Load.Spoke

/-! Actual stress probes decouple the shear tower. Quota formulas below
at filtration 4; transmitted in actual forms. Trace part not presumed zero
or independently normalized.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Analysis Org Extraction Spec Next.UVStress Maxwell
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F:Final C f S}
open UVNext.FreeStress
section wing
variable {L L':Register G}{S:Table L}{S':Table L'}{d:ℕ}{X:S.Rotation}{Y:S'.Rotation}
def zone (J:S.Stress) := Submodule.span ℂ (range fun i: Axis × Axis => J i.1 i.2)
lemma line_mem (J:S.Stress)(p q: Axis):J p q∈ zone J:= Submodule.subset_span (mem_range_self (f:=fun i:Axis×Axis=>J i.1 i.2) (p,q))
lemma cross_line {w:S.Field 4→ₗ[ℂ] S'.Field 4} {J:S.Stress}{P:Submodule ℂ (S'.Field 4)}(h:∀ i j,w (J i j)∈P) {x : S.Field 4}(he:x∈ zone J) : w x∈P := by
   have hy:zone J ≤ P.comap w := Submodule.span_le.mpr (by rintro _ ⟨⟨i,j⟩,rfl⟩;exact h i j)
   exact hy he
def pull (v:S.Field 4→ₗ[ℂ] S'.Field 4) (J:S.Stress)(i j:Axis) : S'.Field 4:= v (J i j)
lemma traceless.passed (v:S.Field 4→ₗ[ℂ] S'.Field 4) {J:S.Stress}(he:traceless X J)(hv:∀ g x,v (X.act 4 g x)=Y.act 4 g (v x)) : traceless Y (pull v J):= by
   refine ⟨fun g i j => ?_,fun i j=> congr_arg v (he.sym i j),?_⟩
   · unfold pull; rw [← hv,he.tensor];simp only [map_sum,map_smul]
   simp only [pull,← map_sum,he.trace,map_zero]
lemma tension {J:S.Stress}(hp:Tensorial X J) : ∀ x∈zone J,∀ v: Ortho,X.act 4 v x∈ zone J:= by
   intro x hx v
   apply cross_line (w:=(X.act 4 v).toLinearMap) _ hx; intro i j
   change X.act 4 v (J i j) ∈ _; rw [hp]
   exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _=>Submodule.smul_mem _ _ (line_mem J i k)
end wing
local notation "Q"=> Bel C.book
local notation "V"=> F.sector.derivatives
local notation "V'"=> Maxwell.Free.scheme C.labels
local notation "σ"=> Maxwell.Free.spin_free C.labels
local notation "E"=> Maxwell.Free.gear C.labels
local notation "α"=> F.sector.turns
local notation "T"=> F.phase.transport
local notation "hY"=> Maxwell.Free.gear_laws C.labels
local notation "H"=> Maxwell.Free.hierarchy C.labels
local notation "Z"=> UVNext.FreeStress.canonicalStress C.labels
local notation "Z'"=> F.sector.energy
variable (hG:G.Simple)
lemma lit_real : Pert.freeStress C.labels=- Z := by
   unfold Pert.freeStress; rw [← Pert.common_stress, torch,one_smul]
include hG
lemma canView : ∃ i j:Axis,Z i j≠0:=by
   by_contra! h; exact can_lit (C:=C) hG (funext fun i=> funext (fun j=>h i j))

lemma absolutely : ∃ p: Module.End ℂ ((Bel C.book).Field 4), Retraction (zone Z) E p ∧ (∀ q,Intervenes E q→∀ x,p (q x)=q (p x)) ∧ p ((Q).unit 4)=0:= by
   obtain ⟨p,hp⟩ := can_project hY (zone Z) (fun x v hx=> tension (single hG).tensor x hx v)
   have hc(w : Module.End ℂ ((Q).Field 4))(hw :Intervenes E w) := hp.central hY (zone Z) (ht:=fun f hf x hx => ?_) hw -- arg U explicit
   rotate_left -- maybe not
   · obtain ⟨t,ht⟩ := coversCrew hG ((single hG).passed f hf)
     apply cross_line _ hx; intro i j
     change pull f _ i j ∈ _; rw [ht]; exact Submodule.smul_mem _ _ (line_mem Z i j)
   refine ⟨p,hp,hc,?_⟩
   let x:= (Q).unit 4; let S:= Submodule.span ℂ {x}
   obtain ⟨q,hq⟩:= can_project hY S (fun v K h=> by
      obtain ⟨c,rfl⟩:= Submodule.mem_span_singleton.mp h
      rw [map_smul, show (E).act 4 K x=x from (hY).identity ..]; exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩ )
   have hh : p x=q (p x):= by conv_lhs => rw [← hq.fixes x (Submodule.subset_span rfl)]; exact hc _ hq.inter_ _
   obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (show p x∈ S from hh.symm ▸ hq.slides _)
   let w:= expectation Q 4; have ht : w (p x)=0 := by
      have hy:zone Z ≤ LinearMap.ker w := Submodule.span_le.mpr (by
          rintro _ ⟨⟨i,j⟩,rfl⟩; rw [← lighting C.labels σ]; exact (kernel_mem.mp (generator C.labels σ).property).2 _ _ )
      exact hy (hp.slides x)
   change p x=0; rw [← ha] at * -- risk
   rw [map_smul,show w x=1 from mean_unit (H).laws] at ht
   rw [show a=0 from (by simpa using ht),zero_smul]

omit hG
abbrev wing (F:Final C f S): S.Stress := delta F.sector.energy
variable {u:Filter (ℕ×ℕ)} (B:Lenses.Mantle F u)(hg:OPE.Services C f S)
local notation "P"=> F.sector.energy
local notation "δ"=> wing F
local notation "W!"=> tent B
local notation "r"=> B.radius -- dangerous
include hg
lemma leading_delta (i j:Axis) : Tendsto (fun k=> (W! k 4).symm (((B.radius k^4:ℝ):ℂ) • (wing F i j))) atTop (𝓝 (- Z i j)) := by
    let w(k):=(B.lens k 4).symm; let ℓ(k:ℕ):ℂ:=↑(r k^4:ℝ)
    have hp (i j:Axis): Tendsto (fun k=> w k (ℓ k • (P i j))) atTop (𝓝 (- Z i j)):=by
        have ht:=stress B hg i j; rw [show Pert.freeStress C.labels= -Z from lit_real] at ht
        exact ht
    have ht:= tendsto_finsetSum Finset.univ (fun i _=> hp i i)
    simp only [Finset.sum_neg_distrib,(single (C:=C) hg.simpleGate).trace,neg_zero] at ht
    apply rent B hg
    by_cases he:i=j
    · change Tendsto (fun k=> w k (ℓ k • (P i j- (if i=j then _ else _)))) atTop (𝓝 _)
      simp_rw [if_pos he,smul_sub,map_sub]
      have hw(k): w k (ℓ k • ((1/4:ℂ) • (sumTrace P)))= (1/4:ℂ) • (∑ a:Axis,w k (ℓ k • P a a)):=by rw [smul_comm (ℓ k),map_smul]; unfold sumTrace;simp only [Finset.smul_sum,map_sum]
      simp_rw [hw]; exact (by simpa only [smul_zero,sub_zero] using ((hp i j).sub ((tendsto_const_nhds (x:=(1/4:ℂ))).smul ht)))
    rw [show wing F i j=P i j from (by simp [wing,delta,he])]; exact hp i j
omit hg in
lemma tent_owns (k:ℕ)(h:IsUnit (shift B k 4)): traceless E (pull (tent B k 4).symm.toLinearMap (wing F)) := delta_traceless (T).spin (T).conserved.symmetric |>.passed _ (fun v x=>
    (tent B k 4).injective (by simp only [LinearEquiv.coe_toLinearMap,tensor_edge B h,LinearEquiv.apply_symm_apply]))
lemma ledger_delta : ∃ f:ℕ→ℂ, Tendsto f atTop (𝓝 (-1)) ∧ ∀ᶠ k in atTop, ∀ i j:Axis,
         (W! k 4).symm (((r k^4:ℝ):ℂ) • (wing F i j))= f k • Z i j:= by
    obtain ⟨p,q,hq⟩:= canView (C:=C) hg.simpleGate
    obtain ⟨F0,hF⟩:= Module.Projective.exists_dual_ne_zero ℂ hq
    let M0 : (Q).Field 4→L[ℂ] ℂ := LinearMap.toContinuousLinearMap F0
    let A(k):= (W! k 4).symm (((B.radius k^4:ℝ):ℂ) • (wing F p q))
    refine ⟨fun k=> M0 (A k)/F0 (Z p q),?_,?_⟩
    · have ht:= (M0.continuous.continuousAt.tendsto.comp (leading_delta B hg p q)).div_const (F0 (Z p q))
      rw [map_neg,neg_div,show M0 (Z p q)=F0 _ from rfl,div_self hF] at ht; exact ht
    filter_upwards [tented B hg 4] with k hk i j
    let b:ℂ:= ((r k^4:ℝ):ℂ)
    obtain ⟨f,hf⟩:= coversCrew hg.simpleGate ((tent_owns B k hk).scale b)
    have he (i j : Axis) : (W! k 4).symm (b • wing F i j)= f • Z i j := by rw [map_smul]; exact congr_fun (congr_fun hf i) j
    change (W! k 4).symm _ = _; rw [he,show A k=f • Z p q from he p q,map_smul]
    rw [show f • M0 (Z p q) / F0 (Z p q)= f from mul_div_cancel_right₀ f hF]
end YM.SharpGram.Load
