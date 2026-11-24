import YM.OPE.Samples.Seats
/-!
# Genetic margin from Steers & prizes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter MeasureTheory Lattice RG Wilson Polar Rhythm MergeProof Ribbons Finset
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C: Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w n A:ℕ} {f:Filter L} {X:L→ I→E4}
    {T:L→ℝ}{R r s: L→ℕ→ℝ} {α:ℕ→ℝ}{q e a b : L→ℝ}{M η:ℝ}
set_option quotPrecheck false
local notation "μ"=> C.S.a
local notation "σ"=> (fun i=> C.path.levels.budget i)
local notation "U"=> Q.localTime H
variable (B: Border f T Q.limit R r α){D:L→Loom Q}{P:ℝ}
variable (h:Oscars B P D C)
namespace Border
-- whole envelope follows from metric only.
variable (hh:H ≤ Q.age Q.star)(hM:0 ≤ M) (hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))
local notation "f!"=> (fun j=> Q.point H (X j))
local notation "Ψ"=> (fun i=> (D i).launch Q.limit)
include hh B hM hX
lemma envelope (hp:t ≤ Q.limit) : ∀ᶠ i in f,∀ j:I, ‖X i j-Q.point H (X i) j t‖ ≤ 2*(M*R i t):=by
    filter_upwards [hX,(eventually_all_finset (Iic Q.limit)).mpr (fun i hi=>eventually_all.mpr fun t': t ≤ i=> B.in_order t' (mem_Iic.mp hi)), (B.ahead hp).pos] with i hi he hp' j using hi.whole hh hp (fun i hu ht=> mul_le_mul_of_nonneg_left (he i (mem_Iic.mpr ht) hu|>.2) hM) (mul_nonneg hM hp'.le)
include h
lemma debounce (hp:t≤Q.limit)(hP:8*M<P): ∀ᶠ i in f,∀ j:I, 4*‖X i j-Q.point H (X i) j t‖ < μ ((D i).below t +1):=by
    filter_upwards [B.envelope hh hM hX hp,h.grab t hp,(B.ahead hp).pos] with i hi hh he j; linarith only [hi j,hh,mul_lt_mul_of_pos_right hP he]
lemma lead_cost (hp:t ≤ Q.limit)(hP:8*M<P) : ∀ᶠ i in f,∀ j:I,4*‖X i j-f! i j (t+1)‖< μ ((D i).launch t):=by
    rcases hp.lt_or_eq with h'|rfl
    · filter_upwards [B.debounce h hh hM hX h' hP] with i hi j using (hi j).trans_le (C.S.strictAnti.antitone ((D i).upper t h'|>.le.trans (Nat.le_succ _)))
    exact Eventually.of_forall fun i j=> (by dsimp only; rw [Q.lead_at (Q.clocked hh|>.2 (show U j < Q.limit+1 from ((Q.timeBirth hh j).trans (Q.bounded _)).trans_lt (Nat.lt_succ_self Q.limit))) (X i),sub_self,norm_zero,mul_zero]; exact C.S.a_pos _)

omit h hM hX hh B
variable {W r' D'}(z:LogPackage C W r' D')(hG:G.Simple)
include z hG
lemma whole_clock (v:ℕ) : ∀ᶠ j in atTop,∃ h:v ≤ j, ∀ p,(σ j).B^2+1 ≤ (C.S.toDepth h p).count.val:=by
    let T:= C.S.scale; have ht:Tendsto T atTop atTop:= C.S.divergent; have hm:Height C.S atTop T id 1:= ⟨tendsto_id,tendsto_const_nhds.congr' ((ht.eventually_gt_atTop 0).mono fun i hi=> (div_self (show T i≠ 0 from hi.ne')).symm)⟩
    have hx:= (height0 (briar C hG z.accounting) hm|>.power 2); let V:= ((hx.add (RateIs.const (c:=1) ht one_pos) ht).mul hm.mesh); filter_upwards [(V.tends (by norm_num) ht).eventually (gt_mem_nhds (C.S.a_pos v)), eventually_ge_atTop v] with i hi he; refine ⟨he,fun p=>?_⟩
    have hz:= C.S.embeds_scale (C.S.toDepth he p); apply (Nat.cast_le (α:=ℝ)).mp; apply le_of_mul_le_mul_left _ (C.S.a_pos i); push_cast; simp only [id] at hi; linarith only [hi,hz]
include B h hM hX hh
structure Sound (X:I→ E4)(S:Loom Q)(v:ℕ)(p:I→ Cover)(C:Family G)(H:ℕ):Prop where
   names : C.S.gridPoint (S.launch Q.limit) ∘ p=X
   laughs : Canvas S C H v p
   comps : Screen X
   avoids i : Q.gap Q.star i < H → i∉ Q.focus H→ ∀ a:Axis,X i a≠0
lemma for_grid (v:ℕ)(P':L→ I→ Cover)(hW:∀ᶠ i in f, C.S.gridPoint ((D i).launch Q.limit) ∘ (P' i)= X i)(hc: 8*M<P)(hη:0<η)(ht:∀ᶠ i in f, Seated Q C (D i) (X i) H) : ∀ᶠ i in f, Sound (X i) (D i) v (P' i) C H:=by
    have hp:= h.lower 0 (Nat.zero_le _); filter_upwards [hW,ht,hX,hp.grows.eventually (whole_clock z hG v), (eventually_all_finset (Iic Q.limit)).mpr (fun i hi=> (B.lead_cost h hh hM hX (mem_Iic.mp hi) hc).and ((B.debounce h hh hM hX (mem_Iic.mp hi) hc).and (peep B hG h (mem_Iic.mp hi) hη)))] with i hi ht hX hv hI
    have hx(j): C.S.gridPoint (Ψ i) (P' i j)=X i j:=congr_fun hi j; let f':= X i
    have hA(j z:I):=GapHomebound (Q:=Q) j z -- pending
    obtain ⟨a,hp⟩:=hv; refine ⟨hi,⟨a,hp,fun t hg j=>hi.symm ▸ ht.neverMind hh hg,fun t hl j=>?_,fun j=>?_,fun j k hk=>?_⟩,?_,?_⟩
    · rw [hx,hi]; exact (hI t (mem_Iic.mpr hl)).2.1 j
    · rw [hx]; exact (ht.provenance hh _).inh ((D i).mono Q (Q.timeBirth hh j) (Q.bounded _))
    · rw [hx,hx]; exact (hI _ (mem_Iic.mpr (hA j k))|>.2.2).trans_lt (hX.reserve j k hk)
    · intro d j k hw; by_contra hz; exact ht.seenParts hh hz rfl ((hI _ (mem_Iic.mpr (hA j k))).1 j) ((hI _ (mem_Iic.mpr (hA j k))).1 k) d hw
    intro j hm hp d; exact ht.virtualSplit hh hp rfl hm ((hI _ (mem_Iic.mpr (hA Q.star j))).1 j) d
-- extra depth guard.Gap nearest outside.
omit h z hG
lemma ear (j:I)(he:j∉ Q.focus H)(hp:t=Q.gap Q.star j)(hl: t < H)(hη:0<η) : ∀ᶠ i in f, η/2*r i t < ‖X i j‖:=by
    have hv:H ≤ Q.limit:= hh.trans (Q.bounded _); have hh': Q.star≠ j:= fun h=>he (h ▸ (Q.on_focus).2 (Q.yes ..))
    have hw:Tendsto (fun i=>R i (t+1)/r i t) f (𝓝 0):= by simpa only [pow_zero,mul_one] using! (B.leap t (hl.trans_le hv) 0)
    have hR:= (hw.const_mul M).eventually (gt_mem_nhds (show M*0 <η/2 from (by rw [mul_zero]; exact half_pos hη)))
    filter_upwards [hX, B.in_order (show t+1≤H from hl) hv,hR,(B.rates t (hl.le.trans hv)).pos] with i hi hA h he; have ht:= hi.reserve Q.star j hh'; rw [← hp] at ht; have he : M*R i (t+1)<η/2*r i t:= (div_lt_iff₀ he).mp (by rw [mul_div_assoc]; exact h); linarith only [mul_le_mul_of_nonneg_left hA.2 hM,he,ht,hi.hostel, norm_sub_le (X i Q.star) (X i j)]
end Border
end YM.OPE.Log.Trunk
