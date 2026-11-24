import YM.WilsonCoeffUV.Winding.Panel
/-! # Local seeds exact Taylor support, winding for canonical Q & actual block penalty. -/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U I α β V:Type*}{i j k r:ℕ}{s a A B t q :ℝ}
variable [Fintype I][DecidableEq α]

lemma iris_owns (b:Leads Cover α I)(P:Gen ℝ I)(r:ℕ)(s:ℝ)(h:0≤s):let A:= (∑ i:Fin r→I, ‖P r i‖)*Real.exp (s*(click b+click b:ℕ)); pairCup (tor n) s A (iris (Option.map (foldUnder n) ∘ b) P r):=by
    intro A; apply iris_design P r _ (D:=click b) _ s h; intro x i j h; set v:= Option.map (foldUnder n) ∘ b; cases hx:b i with
    | none=> simp [v,plank,hx] at h
    | some u=>
        have hy:v i=some (foldUnder n u):=by simp [v,hx]
        rw [plank_origin v _ _ hy,Pi.single_apply] at h; split at h; swap; · simp at h
        rename_i hz; subst j; change size (lift (x+wrap n u.1 - x))≤ click b; rw [add_sub_cancel_left]; exact (wrap_size n u.1).trans (click_mark b hx)

lemma iris_exact_at (b:Leads Cover α I)(x:Cloth α)(p:Cover)(i:I)(v:4*click b<n.val)(h:4*Bank.terrain.gap p x.1<n.val):
    plank (Option.map (foldUnder n) ∘ b) (wrap n p) i (foldUnder n x)= plank b p i x:=by
    set w:= Option.map (foldUnder n) ∘ b; cases hx:b i with
    | none=> simp [w,plank,hx]
    | some u=>
        have ht:w i=some (foldUnder n u):=by simp [w,hx]
        rw [plank_origin w _ _ ht, plank_origin b _ _ hx, ← fold_move]
        have he: foldUnder n x=foldUnder n (jog p u) ↔ x=jog p u:=by
            let z:= (jog p u : Cloth α).1; refine ⟨fun e=>Prod.ext ?_ (show _ from congr_arg (fun x : Co n α=>x.2) e),congr_arg _⟩; have hp :wrap n x.1=wrap n z:= congr_arg Prod.fst e
            have hz:Bank.terrain.gap p z≤click b:=by change size (p+u.1-p)≤_; rw [add_sub_cancel_left]; exact click_mark b hx
            have hv:= nearTau (x:=p) (y:=x.1) (n:=n) (by omega); rw [hp,nearTau (by omega)] at hv; exact sub_left_inj.mp hv.symm
        simp [Pi.single_apply,he]

abbrev priceO (b:Leads Cover α I)(P:Gen ℝ I)(r:ℕ)(s:ℝ):= (∑ i: Fin r→ I, ‖P r i‖)*Real.exp (s*(click b+click b:ℕ))*2*Real.exp (s*4*click b)
lemma iris_R (b:Leads Cover α I)(P:Gen ℝ I)(r:ℕ)(u:0≤s):
     SiteW (iris (Option.map (foldUnder n) ∘ b) P r) (iris b P r) s (priceO b P r s):=by
    let v:= Option.map (foldUnder n) ∘ b; let U:= iris v P r; let X:= iris b P r; let A:=(∑ i: Fin r→ I, ‖P r i‖)*Real.exp (s*(click b+click b:ℕ)); have ht: pairCup (tor n) s A U:=iris_owns b P r s u; have hp:= page_sup b P r s u; let c:= Real.exp (s*4*click b); have hh:1≤ c:= Real.one_le_exp (by positivity); have hx:A≤ priceO b P r s:=by have he:= ht.1; change _≤ A*2*c; nlinarith
    refine ⟨pairMore ht hx,pairMore hp hx,⟨ht.1.trans hx,?_⟩,?_⟩
    · rintro ⟨x,y⟩ a; by_cases w:4*click b<n.val
      · have he:U (slideC n x) (slideC n y)= X x y:=by
             unfold U X iris fade; apply Finset.sum_congr rfl; intro i _; congr 1; exact Finset.prod_congr rfl fun j _=>iris_exact_at b (x j) (y 0).1 (i j) w (vn (vPulse (x:=x) (y:=y)) a)
        change ‖U (slideC n x) (slideC n y)-X x y‖≤_; rw [he,sub_self,norm_zero]; exact mul_nonneg (ht.1.trans hx) (catch_hot ..)
      apply (norm_sub_le ..).trans
      apply le_trans (b:=A+A); · exact add_le_add ((ht.2 ..).trans (mul_le_of_le_one_right ht.1 (catch_peak u _))) ((hp.2 ..).trans (mul_le_of_le_one_right hp.1 (catch_peak u _)))
      have hw : (n.val:ℝ)≤4*click b:=by exact_mod_cast Nat.le_of_not_gt w
      change _ ≤ A*2*c*_
      rw [← mul_two,mul_assoc (A*2)]; apply le_mul_of_one_le_right (mul_nonneg ht.1 (by positivity)); unfold c catchW; rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [mul_le_mul_of_nonneg_left hw u]

    intro a x y; unfold iris fade; apply Finset.sum_congr rfl; intro t _; congr 1; apply Finset.prod_congr rfl; intro i _
    unfold plank; simp only [Function.comp_apply,Matrix.of_apply,show ((jog ((jog a (y 0)).1)).symm (jog a (x i)))=(jog (y 0).1).symm (x i) from Prod.ext (by change -(a+(y 0).1)+(a+(x i).1)= -(y 0).1+(x i).1; abel) rfl]; congr
lemma daisies_period {J:Type*}[Fintype J][Fintype α] {P:Lawn (Co n α)→ℝ}{f:J→Lawn I→ℝ}(h:∀ j,Green (f j)) (A:J→Leads Cover α I) (he:∀ᶠ v : Lawn (Co n α) in 𝓝 0,P v=∑ j:J,∑ x:Site n,f j (casement (A j) x*ᵥ v)) (H:Green P)(k t r):
    sprig P k t r=∑ j:J,wear (iris (Option.map (foldUnder n)∘ A j) (sprig (f j) k t) r):=by
  let b:=f
  let R (j:J)(n:Side)(r): Ten ℝ (Co n α) r:= wear (iris (Option.map (foldUnder n) ∘ A j) (sprig (f j) k t) r)
  symm; change (∑ j:J,R j n r)=_
  by_cases h':r=k+t
  · subst r
    let F (j:J)(x:Site n)(v:Lawn (Co n α)) := f j (casement (A j) x *ᵥ v)
    have hb j x: Green (F j x) := by
      apply ContDiffAt.comp (g:=f j) 0 _ (board _); simp; apply h
    have hy j : Green (∑ x:Site n, F j x):= by
      unfold Green; rw [show (∑ x:Site n,F j x)=fun v=>∑ x:Site n,F j x v from funext fun v=>Finset.sum_apply ..]; apply ContDiffAt.sum; exact fun _ _=>hb ..
    have hv : jet (P)= ∑ j:J,∑ x:Site n, jet (F j x):=by
      rw [show (∑ j:J,∑ x:Site n, jet (F j x))= ∑ j:J, jet (∑ x:Site n,F j x) from Finset.sum_congr rfl (fun j _=> (jet_sum _ _ (fun x _=> hb j x)).symm), ← jet_sum _ _ (fun j _=> hy j)];
      exact jet_congr ((he).mono (fun v hk=> by simpa only [Finset.sum_apply] using hk))
    have hd j : R j n (k+t)= ∑ x:Site n, rye (F j x) (k+t):= by
      unfold R; rw [iris_apply]; apply Finset.sum_congr rfl; intro x _;
      have he: sprig (f j) k t=sprig (f j) (k+t) 0:= by simp [sprig]
      rw [he,← beam (casement (A j) x) (f j) (h j),sprig, Nat.add_zero,shine_lit]
    simp_rw [hd,sprig,shine_lit]; apply unique_kernel (Smooth.sum _ ) (rye_sym (H) _); swap; exact fun i _=> Smooth.sum fun j _=>rye_sym (hb ..) _
    rw [← jet_apply, hv]; simp_rw [map_sum]; simp only [jet_apply]
  unfold R; rw [sprig,shine_dark (Ne.symm h')]; apply Finset.sum_eq_zero; intro i _; rw [iris_apply]; apply Finset.sum_eq_zero; intro x _; funext v; unfold fade; simp_rw [sprig,shine_dark (Ne.symm h')]; simp
lemma daisySight {J:Type*}[Fintype J][Fintype α] {P:(n:Side)→ Lawn (Co n α)→ℝ}{b:J→ Lawn I→ℝ}(h:∀ j,Green (b j)) (A:J→Leads Cover α I) (he:∀ n:Side,∀ᶠ v : Lawn (Co n α) in 𝓝 0, P n v=∑ j:J,∑ x:Site n,b j (casement (A j) x*ᵥ v)) (H:∀ n,Green (P n))(k t r)(s:ℝ)(v:0<s):∃ C:ℝ,∀ n:Side,Sight (sprig (P n) k t r) ((∑ j:J,sunflower (A j) (sprig (b j) k t)) r) s C:=by
    set u:=32*s; have hx:0<u:=by unfold u; positivity
    let V j:= priceM (ULift.{0} Unit) 1 u * priceO (A j) (sprig (b j) k t) r u
    refine ⟨∑ i,V i,fun n=>?_⟩; rw [daisies_period h A (he n) (H n),Finset.sum_apply]; apply Sight.sum; intro i _; have ht:=SiteW.worthy (iris_R (n:=n) (A i) (sprig (b i) k t) r hx.le) hx; rwa [show u/32=s from by unfold u; ring] at ht
section
variable {G:Gauge}{P:Patch}{C:KernelChoices}{Ñ:ChartRatio G}
omit [Fintype I][DecidableEq α] in
lemma meterSun (h:LocalRatio Ñ)(k r)(s:ℝ)(p:0<s):∃ A:ℝ,∀ n:Side,Sight (sprig (unhaar (n:=n) Ñ) 0 k r) (bearingJ Ñ k r) s A:=by
   apply daisySight (I:=G.ColorIndex) (h:=fun _=> blume_green h) (A:=bekon G) (P:=fun n=> unhaar (n:=n) Ñ) _ (fun _=> unhaar_green h) 0 k r s p; intro n; apply Eventually.of_forall; intro v; unfold unhaar; rw [Fintype.sum_prod_type,Finset.sum_comm]; exact Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl fun i _=>by rw [beckons]; rfl)
omit [Fintype I][DecidableEq α] in
lemma meterZen (h:P.Branches C G)(k r)(s:ℝ)(p:0<s):∃ A:ℝ,∀ n:Side,Sight (bend (weaveH (ratioN P.L n) G) (sprig (jointPen G (stepAt P C n)) 2 k) r) (warren P C G k r) s A:=by
    simp_rw [pick_page P C _ h]; exact daisySight (α:=Hinge G P.L) (I:=AudienceK P G) (J:=Axis) (b:=fun v=> debit (G:=G) P C v) (P:=fun n u=> jointPen G (stepAt P C n) (u ∘ weaveH (ratioN P.L n) G)) (fun j=>debut_green (stepAt P C 1) j h) (fun _=>seat P G) (fun n=>(P_perch P C h n).2) (fun n=>(P_perch P C h n).1) 2 k r s p
end
end YM.WilsonCoeffUV.Winding
