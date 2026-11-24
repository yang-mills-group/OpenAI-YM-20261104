import YM.MSbar.Tilt.Rifts
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Positions (Primary n G)
local notation "V"=> G.Color
variable (z:Site n→G.Color) (x:Positions (Primary n G))
variable {R B C D E t c:ℝ}
local notation "L"=> tint G (Body 1 n)
variable (F: Rep G n)(f:Nesting G n)(x' :Positions (Primary n G))(p:ℕ)(V':Finset (Body 1 n))
variable {A b B U a:ℝ}{α:ℝ→ Config G n→ℝ}
variable (hf:Trend α f F.path F.clip p)
local notation "q"=> hung F f t p z
variable (ha: ∀ i≤p,Stone G i 2 E b)(hr:t >0)(hr':t ≤1)
local notation "f!"=> fun i=> atlas f p i F.path F.clip
variable (hQ:∀ i≤p,∀ x:Positions (Primary n G), ‖tint G _ x‖ ≤ A → ∀ j:Primary n G, |fderiv ℝ (atlas f p i F.path F.clip) x (bolt j)| ≤ B ∧ ∑ u:Primary n G, |buoy (atlas f p i F.path F.clip) x [u,j]| ≤ B)
variable (he: t*A<E) (hp: 1≤A)
local notation "P!"=> costP
variable (h:Guide G C D) (hh: t*R<C)(hk:t*R<E)(hX:‖tint G _ x‖≤R)(hY:‖tint G _ x'‖≤R) (hz:∀ i:Body 1 n, ‖ran z i‖ ≤ R)
local notation "u₀"=>reset z t
lemma offset : L (grad z)=fun i=>(ran z i).2-(ran z i).1:=by rw [←speedStart,speedsK, ContinuousLinearEquiv.apply_symm_apply,map_zero]; exact funext fun i=> Native.Chart.begins ..
include h hh hX hz hr
local notation "u!"=> D*t*R^2
lemma wax(s:ℝ)(hs:|s|≤1): ‖tint G _ (reset z t x s)‖≤ 3*R+D*t*R^2:=by
     let U:=regal z x s; have he:=pinch z x h hr hX hz hh s hs; have hy:‖L U‖ ≤ 3*R:=by
          have hg:‖L (grad z)‖≤ R+R:=by
            refine pi_norm_le_iff_of_nonneg (by have hx:0≤R:= (norm_nonneg _).trans hX; positivity)|>.mpr (fun i=>?_); rw [offset]; apply (norm_sub_le ..).trans; let u:=ran z i; exact add_le_add ((le_max_right ‖u.1‖ ‖u.2‖).trans (hz i)) ((le_max_left ‖u.1‖ ‖u.2‖).trans (hz i))
          unfold U regal; rw [map_add,map_smul]; refine (norm_add_le ..).trans ((add_le_add hX ?_).trans_eq (by ring : R+(R+R)= _)); rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) hs).trans hg
     rw [map_sub] at he; exact (show ‖L (u₀ x s)‖ ≤ ‖L (u₀ x s)- L U‖+ ‖L U‖ from (by nth_rw 1 [show L (u₀ x s)=L (u₀ x s)- L U+ L U from (by abel)]; exact norm_add_le ..)).trans ((add_le_add he hy).trans_eq (add_comm ..)) -- lemma
omit h hh hX hz hr
local notation "V₁"=> V' ×ˢ (Finset.univ :Finset G.ColorIndex)
lemma tin {A B:Positions (Primary n G)}{C:ℝ}(h:∑ i∈ V', (1:ℝ)≥0)(hv:∀ i : Primary n G,i.1∉ V' → A i=B i) (he: ∀ i:Primary n G,|B i-A i| ≤ C): moves A B≤ ((V'.card *G.lieDim:ℕ)*C):=by
     unfold moves; rw [← Finset.sum_subset (Finset.subset_univ V₁) (fun i _ hg=> ?_ )]; · exact (Finset.sum_le_sum (fun i _=> he i)).trans_eq (by rw [sum_const,nsmul_eq_mul, card_product,card_univ,Fintype.card_fin])
     have hx:i.1∉V':=by intro h;apply hg;exact Finset.mem_product.mpr ⟨h,mem_univ _⟩
     rw [hv i hx,sub_self,abs_zero]
variable (hG:∀ i:Body 1 n,i∉ V' → tint G _ x i=tint G _ x' i)
local notation "Ψ"=> film F f t p
include h hh hX hY hz hr hG
variable {ω₀ W':ℝ}
lemma nerve (ha₀: ‖regal z x 1‖+u! ≤ ω₀) (ha₁: ‖regal z x' 1‖+u! ≤ ω₀) (hτ:∀ x:Positions (Primary n G),x∈ Metric.closedBall 0 ω₀ → ContDiffAt ℝ (↑(2:ℕ)) (film F f t p) x ∧ (∀ i:Primary n G,|fderiv ℝ (film F f t p) x (bolt i)| ≤ U)∧ ∀ i:Primary n G,∑ j:Primary n G, |buoy (film F f t p) x [j,i]|≤ U)(hw:0 ≤ U) :
       let T:= film F f t p
       |(T (reset z t x' 1)-T (reset z t x 1)) -(T (regal z x' 1) - T (regal z x 1))| ≤ U*((V'.card *G.lieDim:ℕ)*(2*(D*t*R^2))) +U*(D*t*R^2)* ((V'.card*G.lieDim:ℕ)*(2*ω₀)) :=by
       intro T; let J:=regal z x 1; let J':=regal z x' 1; let Y:= u₀ x 1; let Y':=u₀ x' 1; let S:=Metric.closedBall (0:K) ω₀
       have hx(v:K) (h':‖tint G _ v‖ ≤ R):‖reset z t v 1-regal z v 1‖ ≤ D*t*R^2:=by
             have hv(v:K):‖v‖ ≤‖L v‖:=by refine pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr fun i=>?_ ; exact le_trans (show ‖v i‖ ≤ ‖L v i.1‖ from PiLp.norm_apply_le (L v i.1) i.2) (norm_le_pi_norm _ _)
             exact (hv _).trans (pinch z v h hr h' hz hh 1 (by simp)) -- K.P
       have ht:‖Y-J‖ ≤ D*t*R^2:=hx _ hX; have ht':‖Y'-J'‖ ≤D*t*R^2:=hx _ hY
       let xK : 0 ≤ u! :=(norm_nonneg _).trans ht; have hJ:‖J‖≤ ω₀ := (le_add_of_nonneg_right xK).trans ha₀; have hJ':‖J'‖ ≤ ω₀:= (le_add_of_nonneg_right xK).trans ha₁
       have hd(X Z:K): ‖X‖ ≤ ‖X-Z‖+ ‖Z‖:=by nth_rw 1 [show X=X-Z+Z from (by abel)]; exact norm_add_le ..
       apply (Tilt.soar T (convex_closedBall 0 ω₀) (mem_closedBall_zero_iff.mpr hJ) (mem_closedBall_zero_iff.mpr (((hd Y J).trans (add_le_add_left ht _)).trans ((add_comm ..).trans_le ha₀))) (mem_closedBall_zero_iff.mpr hJ') (mem_closedBall_zero_iff.mpr (((hd Y' J').trans (add_le_add_left ht' _)).trans ((add_comm ..).trans_le ha₁))) ht ht' hw hτ).trans
       have hu(i:Primary n G)(hi:i.1∉V'): J' i=J i∧Y' i=Y i:=by
            have hu: x' i=x i:= congr_arg (fun u:V=>u i.2) (hG _ hi|>.symm); constructor; · unfold J J' regal; rw [Pi.add_apply,Pi.add_apply,hu]
            unfold Y Y' reset; rw [Pi.smul_apply, Pi.smul_apply]; apply congr_arg; apply congrArg (fun v:G.Color=>v i.2) (show Native.Chart.head G (ran z i.1) (1*t,L (t •x') i.1)=Native.Chart.head G (ran z i.1) (1*t,L (t •x) i.1) from (by rw [map_smul,map_smul, Pi.smul_apply,Pi.smul_apply,hG i.1 hi]))
       have he:0≤ ∑ i∈V',(1:ℝ):=Finset.sum_nonneg fun i _=>zero_le_one; refine add_le_add (mul_le_mul_of_nonneg_left ?_ hw) (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hw xK))
       · apply Tilt.tin V' he; · intro i hi; change J' i-J i=Y' i-Y i; rw [(hu i hi).1,(hu i hi).2,sub_self,sub_self]
         intro i; change |Y' i-Y i-(J' i-J i)| ≤ _; rw [show Y' i-Y i-(J' i-J i)=Y' i-J' i-(Y i-J i) from (by ring)]; exact (abs_sub ..).trans ((add_le_add ((norm_le_pi_norm (Y'-J') i).trans ht') ((norm_le_pi_norm (Y-J) i).trans ht)).trans_eq (two_mul _).symm)
       exact Tilt.tin V' he (fun i hi=> (hu _ hi).1.symm) (fun i=> (abs_sub ..).trans ((add_le_add ((norm_le_pi_norm J' i).trans hJ') ((norm_le_pi_norm J i).trans hJ)).trans_eq (two_mul _).symm))
include hQ hf ha he hr' hp hk
lemma Xact (hB:0≤ B)(hx: 3*R+D*t*R^2≤ A) (ha₀: ‖regal z x 1‖+u! ≤ ω₀) (ha₁: ‖regal z x' 1‖+u! ≤ ω₀) (hτ:∀ x:Positions (Primary n G),x∈ Metric.closedBall 0 ω₀ → ContDiffAt ℝ (↑(2:ℕ)) (film F f t p) x ∧ (∀ i:Primary n G,|fderiv ℝ (film F f t p) x (bolt i)| ≤ U)∧ ∀ i:Primary n G,∑ j:Primary n G, |buoy (film F f t p) x [j,i]|≤ U)(hw:0 ≤ U)(hF:Touch F.eval):
       let n₁:= (V'.card*G.lieDim:ℕ); let H:= film F f t p; let W:= ore F f t p
       |Real.log (F.eval (postcard G n t x'))-Real.log (F.eval (postcard G n t x)) -(W x'-W x) -(H (regal z x' 1)-H (regal z x 1))|
         ≤ U*(n₁*(2*(D*t*R^2))) +U*(D*t*R^2)* (n₁*(2*ω₀)) + coal G p b R t A B * (n₁*(A+A)):=by
        intro n₁ f1 W';
        have hZ :=tap z x F f x' p V' hf ha hr hr' hQ he hp h hh hk hX hY hz hG (fun s hx' hy'=>by refine ⟨(wax z x hr h hh hX hz s ((abs_of_nonneg hx').trans_le hy')).trans hx,(wax z x' hr h hh hY hz s ((abs_of_nonneg hx').trans_le hy')).trans hx⟩) hB -- order
        let v:K:= u₀ x 1; let v':K:= u₀ x' 1; have H:= Tilt.nerve z x F f x' p V' hr h hh hX hY hz hG ha₀ ha₁ hτ hw
        apply le_trans (le_of_eq _) ((abs_add_le ..).trans (add_le_add H hZ)); apply congr_arg; let c(X:K):= u₀ X 1; have he(X:K)(hx: ‖tint G _ X‖≤ R): Real.log (F.eval (postcard G n t X))= f1 (c X)+W' (c X):=by unfold f1 W' film; rw [Pi.sub_apply,sub_add_cancel]; change Real.log _ =Real.log (F.eval (postcard G n t (reset z t X 1))); rw [taper z _ h hr hx hz hh 1 (by simp),hF.shield]
        rw [he x hX, he x' hY]; change f1 v'+W' v' - (f1 v+W' v) - (W' x'-W' x) - _= _; unfold v v' f1 W'; ring
end YM.MSbar.Tilt
