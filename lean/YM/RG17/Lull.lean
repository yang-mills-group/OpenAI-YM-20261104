import YM.RG17.Storm
/-!
# From Served on that polynomial obtain THIS actual relative error estimate
 on a specific zero-flag **sector** (V! not errors across changing cutoff!!).
 Non-Taylor: replace ${$body$}$ multiple soft insertion conditional at that
 stop by literal SINGLETON regular product. Don't interpret it as gaussian dominance on period. Use mode weights!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Finset Function Filter MeasureTheory Lattice RG Pressure Wilson Marker Source Overlay Extra.Histories
open FullVolume.Sever MergeProof MergeProof.Accent Motion Extra.Trajectories Extra.Multi Next.Rank Edition Spindle
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
section zero
variable {n k:ℕ} {G:Gauge}{Γ:Census (Fin n)}{p:Side}
private lemma voidLeaf (T:Activities G p) (g:ℕ→ Config G p→ℂ)(Q: MergeProof.Box p)(hq:Q.2=∅)(U:Config G p): profile T g Q U=0:=by
    have he : IsEmpty {i//barcode T i=Q}:=by
       refine ⟨fun ⟨i,hi⟩=>?_⟩
       have ht:(T.forced i).inventory=∅:= (show _=_ from congr_arg Prod.snd hi).trans hq
       exact (T.forced i).inventory_ne.ne_empty ht
    exact tsum_empty
-- pattern DOES NOT force every member to have nonempty inventory; good ports required on per sector.
private lemma quietField (T: MergeProof.Box p→Poly Γ)(ht:∀ i,i.2=∅→ T i=0): Accent.field T ∅=1:=by
   unfold Accent.field; rw [Finset.sum_eq_single_of_mem (a:=∅) (by simp)]
   · rw [Accent.grid,if_pos (by simp [Accent.Pattern]),Finset.prod_empty]
   intro b hb he
   unfold Accent.grid; split
   next H=> obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr he; apply Finset.prod_eq_zero hi (ht i ?_)
            exact Finset.eq_empty_iff_forall_notMem.mpr (fun x hx=> Finset.notMem_empty _ (H.2 ▸ Finset.mem_biUnion.mpr (show ∃ j ∈ b,x∈j.snd from ⟨i,hi,hx⟩))) -- syntax
   next=> exact rfl

variable {R: Rep G p}{x:Fin n→Site p}{F:Fin n→ Config G p→ℂ} (S:Fin n→ℕ → Config G p→ℂ) {H: Support p → Config G p→ Poly Γ}{K: MergeProof.Box p→ Config G p→ Poly Γ}
local notation "Gx"=> fun i : Fin n=> profile R.activities (S i)
local notation "J"=> fun z:ℂ=>restore R F Gx (z • H) (z • K)
lemma clearLeaf (hp:Carton x H K R.p.threshold)(U:Config G p) (hh: flags R.p.threshold U=∅)(z:ℂ) :
        restore R F (fun i=> profile R.activities (S i)) (z • H) (z • K) U=
        (R.eval U:ℂ) • Poly.pass (Mach Γ (fun i=> F i U)+ ∑ i, z • H i U):=by
   have ha:R.eval U=Real.exp (R.exponent U):=by rw [Rep.eval,Activities.gas_one _ _ hh,mul_one]
   unfold restore; rw [hh,quietField,mul_one,ha]; swap
   · intro i hi
     let K':=(z • K) i U
     have hg:K'=0:= by by_contra hv; exact ((lit hp z |>.flag i).1.permits U hv|>.2.1.ne_empty) hi
     rw [show (z • K) i U=_ from hg,bar,voidLeaf _ _ i hi,Mach,sum_eq_zero,Poly.bead]; swap -- name?
     · intro j _; dsimp only; rw [voidLeaf _ _ i hi,Poly.send_zero]
     · simp -- extra goals?
   rfl

lemma clearZero (hp:Carton x H K R.p.threshold)(U:Config G p) (hh: flags R.p.threshold U=∅)(s:Γ.Mode) :
   ((J 0 U).part s)= (R.eval U:ℂ) * ∏ j∈s.val, F j U:=by
     dsimp only; rw [clearLeaf S hp U hh 0]; simp_rw [zero_smul,sum_const_zero,add_zero]; exact (Poly.part_smul ..).trans (congr_arg _ (Extra.Trajectories.pass_fire ..))
variable {P:Config G p→Poly Γ}{a e b:ℝ}{w:Fin n→ℝ}
lemma gentleScene (hx:Served R F (fun i=> profile R.activities (S i)) P x w e a) (hy:Vault w F (fun i=> profile R.activities (S i)) b 1)
    (hw:∀ i,0<w i)(he:0≤e-2) (hc: Drake Γ R.p.B x)(hr:8≤R.p.B)(hz:2 < brisk R.p.B) (U:Config G p)(ht: flags R.p.threshold U=∅) (s:Γ.Mode):
    ‖(P U).part s/(R.eval U:ℂ) - ∏ j∈ s.val,F j U‖ ≤ Real.exp ((n:ℝ)*(b+a)) / Poly.toll w s / (brisk R.p.B / 2):=by
    obtain ⟨H,K,h,hH,hK,hp⟩:= hx
    let k(i V):= profile R.activities (S i) V
    let L(z:ℂ):= restore R F (fun i=> profile R.activities (S i)) (z • H) (z • K) U
    let D:=R.eval U
    have hv:D=Real.exp (R.exponent U):=by unfold D; rw [Rep.eval, Activities.gas_one _ _ ht,mul_one]
    have hg':(D:ℂ)≠0:= Complex.ofReal_ne_zero.mpr ((hv.symm ▸ Real.exp_pos _).ne')
    let Y(z:ℂ):=(L z).part s / D
    have hj:Differentiable ℂ Y:=(Lamps.zoom F (fun i=> profile R.activities (S i)) R U H K s).div_const _
    have hm(z:ℂ)(hh:z∈Metric.ball (0:ℂ) (brisk R.p.B)): ‖Y z‖ ≤ Real.exp ((n:ℝ)*(b+a))/Poly.toll w s:= by
       have hk:‖z‖ ≤ brisk R.p.B:= (by simpa using hh : ‖z‖ < _).le
       let V(i : Support p) W:= z • H i W
       let Z:= Mach Γ (fun i=> F i U)+ ∑ i,V i U
       have hB: L z=(D:ℂ) • Poly.pass Z:= clearLeaf S h U ht z
       have hh: Towed w id V R.p.B (e-2) a:= incur hc hr (fun i=> (h.exp i).1.toBorne) (fun i=> (h.exp i).2) hH hw z hk
       have hM: Poly.price w Z ≤ n*(b+a):=by
            apply (Poly.addition hw ..).trans
            rw [mul_add]; apply add_le_add
            · apply (Poly.batch hw ..).trans
              simp_rw [Poly.solo,Poly.solo_toll]; exact (Finset.sum_le_sum (fun i _=>hy.exp i U)).trans_eq (by simp)
            have hV(i): Burns x i (V i) R.p.threshold ∧ ∀ U,rises (V i U):= lit h z |>.exp i
            refine (Poly.batch hw ..).trans ?_
            have hQ:= harvest hh hw he U x (fun i hi=> touchdown (hV i).1.toBorne U hi ((hV i).2 U))
            simpa only [Fintype.card_fin] using hQ
       unfold Y; rw [hB,Poly.part_smul,mul_comm (D:ℂ),mul_div_cancel_right₀ _ hg']; apply (le_div_iff₀ (Poly.worth hw _)).mpr; rw [mul_comm]; exact (Poly.member hw ..).trans ((Poly.pass_budget hw Z).trans (Real.exp_monotone hM))
    have hs:L 1=P U:=by rw [hp]; unfold L; simp only [one_smul]
    have hh₀:Y 0=∏ j∈s.val,F j U:=by unfold Y L; rw [clearZero S h U ht s, mul_comm (R.eval U:ℂ),mul_div_cancel_right₀ _ hg']
    have hc:= touch Y _ _ hz hj.differentiableOn hm
    exact (show Y 1=_ from congr_arg (fun Z:Poly Γ=> Z.part s / (D:ℂ)) hs) ▸ (hh₀ ▸ hc)
end zero
end YM.RG17
