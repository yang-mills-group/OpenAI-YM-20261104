import YM.MSbar.Pole.Scale.Closed

/-! Transfer a differential RG identity to the pole coefficients, including
subdivergences/coefficientwise finite limits. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Curtain
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I] {F G : ℝ → ℂ → Cloud I} {A : Finset I} {d:Age}
variable {k:ℕ}

/-- pointwise version, preserving boundary against any finite limits. -/
lemma point_pole {k:ℕ} (C:ℕ→ℂ) (K:ℂ) (h:Tendsto (fun z:ℂ=>∑ i∈Finset.range k,z⁻¹^(i+1)*C i) approaching (nhds K)) : ∀ i<k,C i=0 := by
  induction k with
  | zero=> intro i hi; omega
  | succ k ih=>
    have hT : Tendsto id approaching (nhds (0:ℂ)):= Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
    have ht := (hT.pow (k+1)).mul h
    have hv : Tendsto (fun z:ℂ => (∑ i∈Finset.range k,z^(k-i)*C i)+ C k) approaching (nhds (C k)):= by
      let g (z:ℂ):=(∑ i∈Finset.range k,z^(k-i)*C i)+C k
      have he : g 0=C k:=by unfold g; rw [Finset.sum_eq_zero]; simp; intro i hi; simp [show k-i≠0 by simp at hi; omega]
      apply Eq.subst (motive:=fun w=>Tendsto g approaching (nhds w)) he ((show Continuous g from by unfold g; fun_prop).continuousAt.continuousWithinAt)
    simp only [id_eq,zero_pow (by omega : k+1≠0),zero_mul] at ht
    have he : C k=0:= by
      apply tendsto_nhds_unique_of_eventuallyEq hv ht
      filter_upwards [(self_mem_nhdsWithin (a:=(0:ℂ)) (s:={0}ᶜ))] with z hz; have ha:z≠0:=hz
      rw [Finset.sum_range_succ,mul_add]; congr 1
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=> ?_
        rw [show k+1=k-i+(i+1) by simp at hi; omega,pow_add, inv_pow,mul_assoc (a:=z^(k-i)),mul_inv_cancel_left₀ (pow_ne_zero _ ha)]
      rw [inv_pow,mul_inv_cancel_left₀ (pow_ne_zero _ ha)]
    intro i hi; rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hh|hh
    · exact ih (by simpa [Finset.sum_range_succ,he] using h) i hh
    rw [hh]; exact he

lemma fried (h : Soft F) (n : ℕ) (x : External I n) {r : ℝ} (hr : 0<r) :
    (∀ᶠ z in approaching,DifferentiableAt ℝ (fun s=>F s z n x) r) ∧ ∃ c : ℂ,Tendsto (fun z => deriv (fun s=>F s z n x) r) approaching (nhds c):=by
  obtain ⟨g,hg,hb⟩:=h.discrete r hr n x
  let D(p : ℝ × ℂ):= fderiv ℝ g p (1,0)
  have hc : ContinuousAt (fun z:ℂ=> D (r,z)) 0:= ((hg.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).comp (continuousAt_const.prodMk continuousAt_id)
  have ha : ∀ᶠ z in approaching, ∀ᶠ s in nhds r,F s z n x=g (s,z):=by
    have hm : ∀ᶠ v in nhds (r,(0:ℂ)), v.2≠0→F v.1 v.2 n x=g v:=hb
    rw [nhds_prod_eq] at hm
    obtain ⟨p,hp,q,hq,hs⟩:= eventually_prod_iff.mp hm
    filter_upwards [hq.filter_mono (show approaching ≤ _ from nhdsWithin_le_nhds),self_mem_nhdsWithin (s:={(0:ℂ)}ᶜ)] with z hz ht
    exact hp.mono fun i hi=>hs hi hz ht
  have hf : ∀ᶠ z in approaching,HasDerivAt (fun s=>F s z n x) (D (r,z)) r := by
    have hm : ∀ᶠ z in nhds (0:ℂ),ContDiffAt ℝ 1 g (r,z) := (show ContinuousAt (fun z:ℂ=> (r,z)) 0 from continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hg.eventually (by simp))
    filter_upwards [ha, hm.filter_mono (show approaching ≤ _ from nhdsWithin_le_nhds)] with i hi hk
    exact (show HasDerivAt (fun t:ℝ=>g (t,i)) (D (r,i)) r from (((hk.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r i)))).congr_of_eventuallyEq hi
  exact ⟨hf.mono fun i hi=>hi.differentiableAt,_,Filter.Tendsto.congr' (hf.mono fun i hi => hi.deriv.symm) hc.continuousWithinAt⟩ -- hc already ContinuousAt

variable {M : ℕ → ℝ → Cloud I} {a:ℤ}
theorem stiffness (D : ∀ i, Ledger A a (M i)) (hF : Soft (F-polar k M))
    (h : ∀ (r:ℝ),0<r→ Vortex 0 (G r))
    (hh : ∀ n x (r :ℝ),0<r→ ∀ᶠ z in approaching,HasDerivAt (fun s=> F s z n x) ((r:ℂ)⁻¹*G r z n x) r) :
    ∀ n x (r:ℝ), 0<r→∀ i<k,deriv (fun s=> M i s n x) r=0:= by
  intro n x r hr
  obtain ⟨R,H,hp,hQ,hz⟩:= h _ hr
  obtain ⟨hm,c,hc⟩:=fried hF n x hr
  have hi : Tendsto (fun z=> (r:ℂ)⁻¹ *G r z n x) approaching (nhds ((r:ℂ)⁻¹ * H 0 n x)):= by
    apply Filter.Tendsto.congr' (f₁:=fun z=> (r:ℂ)⁻¹ * H z n x) ?_ (((continuousAt_const.mul (((hQ.budget n).region 0 (zone_zero hp) x).continuousAt))).continuousWithinAt)
    filter_upwards [neighborhood hp] with z h'; rw [← hz z h']; simp
  let Q (i : ℕ):= deriv (fun s=> M i s n x) r
  refine point_pole Q _ (Filter.Tendsto.congr' ?_ (hi.sub hc))
  filter_upwards [hh n x r hr,hm] with z hu hl
  let P(s:ℝ):= polar k M s z n x; let B := ∑ i∈Finset.range k,z⁻¹^(i+1)*Q i
  have hb : HasDerivAt P B r:=by
    apply (HasDerivAt.fun_sum (u:=Finset.range k) (A:=fun i s=> z⁻¹^(i+1) * M i s n x) (A':=fun i=> z⁻¹^(i+1)*Q i) (fun i _=>?_)).congr_of_eventuallyEq
    · exact Eventually.of_forall fun i=>by simp [P,polar,purePolar]
    exact (((D i).smooth hr n x).differentiableAt (by simp)).hasDerivAt.const_mul _
  change (r:ℂ)⁻¹ *_- deriv ( (fun s=>F s z n x)- P) r = _; rw [(hu.sub hb).deriv]; ring
lemma nailed (D : ∀ i, Ledger A a (M i)) (h : ∀ n x (r:ℝ), 0<r→∀ i<k,deriv (fun s=> M i s n x) r=0) (i:ℕ) (hi:i<k) {r:ℝ} (hr:0<r) : M i r=M i 1:= by
  funext n x
  apply IsOpen.is_const_of_deriv_eq_zero (𝕜:=ℝ) isOpen_Ioi (convex_Ioi (0:ℝ)).isPreconnected
    (fun z hz => ((D i).smooth hz n x).differentiableAt (by simp)|>.differentiableWithinAt) (fun z hz=> h n x z hz i hi) hr (show (0:ℝ)<1 from zero_lt_one)
end YM.MSbar.Pole.Curtain
