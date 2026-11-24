import YM.MSbar.Tramp.Whim
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Matrix
open Precision Gauge Midpoint Rolling Wave MvPolynomial Exterior Tree Wilson Laurent Bloch
open AnalyticBridge.VerifiedReset Native.Chart Tensor UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio) (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1))
local notation "X"=> Primary n G
local notation "Y"=> Primary c G
local notation "T"=>S.ratio
local notation "A"=>T.count
local notation "R"=>installed T P
local notation "D"=>(S.patch.L.val:ℝ)
local notation "L"=>Measuring.chart n G
noncomputable def path (T': Ratio c n) (G:Gauge) (i: Primary c G) : Site n:= T'.embed (Measuring.chart c G i)
local notation "O"=>path S.ratio G
local notation "U"=> slide G n
variable {s:ℕ} {b a C' B E δ:ℝ}(ha:0<a)(hp:P.strip a C')(hx:0≤ C')
noncomputable def premob (S:Patch)(a C:ℝ) := stackFee a C (TypeFace 1)*(S.L.val:ℝ)
noncomputable def tranche (S:Patch)(a C:ℝ) :ℝ:= let κ:=premob S a C; κ +(1+UVNext.PricedKernels.dC 0 a*hikeC S.J a)*κ +hikeC S.J a * κ
local notation "f₀"=>premob S.patch a C'
local notation "κ"=>tranche S.patch a C'
lemma cardP : Multiplicity (path S.ratio G) (tintCost G):=flagC T (Measuring.chart c G) (starM G c)
include hp ha hx
lemma memberP : Annuity (site n _) (parent S.ratio _) (installed T P) (a/D) (premob S.patch a C'/D) :=by
    apply (Annuity.paid_cross hp ha.le).cut le_rfl; unfold premob stackFee; rw [mul_div_cancel_right₀ _ (by positivity)]
variable (t:ℝ) (ht:t∈ Set.Icc (0:ℝ) 1) (i:Cards G n)(j:Primary c G)
lemma funds0 :0≤tranche S.patch a C' :=by
    have ht:= stackFee_nonneg a (TypeFace 1) hx; have hp:=hikeC_pos S.patch.J a; have hv:= dC_nonneg 0 a; unfold tranche; unfold premob; positivity
include ht
lemma feet : gained (a/D) (slide G n i) (path S.ratio G j) * |mouth F (installed T P) t G i j| ≤ tranche S.patch a C':=by
    have hp:0 ≤ f₀:=mul_nonneg (stackFee_nonneg _ _ hx) (by positivity); let p:= site n (TypeFace 1); let q:= parent S.ratio (TypeFace 1); let v:=a/D; have hx' (w:Body 1 n): gained v w.1 (O j) * |R w j.1| ≤ f₀:=by
        have he:0 ≤ gained v w.1 (O j) := gained_pos ..|>.le; have hP:= (memberP P ha ‹P.strip _ _› hx) w
        refine (Finset.single_le_sum (fun i _=>mul_nonneg (gained_pos v w.1 (q i)|>.le) (abs_nonneg (R w i))) (Finset.mem_univ j.1)).trans (hP.trans ?_); exact div_le_self hp (by exact_mod_cast S.patch.L.property)
    let C₀:=hikeC S.patch.J a; have hh:=hikeC_pos S.patch.J a; let K':=(1+UVNext.PricedKernels.dC 0 a*C₀)*f₀; have hk:0≤K':=by have hm:=dC_nonneg 0 a; unfold K'; unfold C₀; positivity
    have he:=memberP P ha ‹P.strip _ _› hx; cases i with
    | inl i=>
       let p:= i.1; let W:= gained v p.1 (O j); have hw:0≤W:= gained_pos ..|>.le; let J:= extracted S F R; have ht' : W*|J i.1 j.1|≤ K':=by
           have hz:= (extract_price S a ha.le F R f₀ hp he) i.1; exact (Finset.single_le_sum (s:=Finset.univ) (f:=fun t=>gained v p.1 (q t)*|J i.1 t|) (fun i _=> mul_nonneg (gained_pos ..|>.le) (abs_nonneg _)) (Finset.mem_univ j.1)).trans hz
       change W*|(1-t)*maple R G i j+t*shuttle F R i j| ≤ _; by_cases H:i.2=j.2
       · rw [maple,shuttle,maple]; simp only [Matrix.of_apply,H,↓reduceIte]; apply (mul_le_mul_of_nonneg_left (abs_add_le ..) hw).trans; rw [mul_add,abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ 1-t by linarith only [ht.2]),abs_of_nonneg ht.1]
         refine (add_le_add (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) (by linarith only [ht.1])) hw) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) ht.2) hw)).trans ((add_le_add (hx' p) ht').trans (le_add_of_nonneg_right (mul_nonneg (hikeC_pos ..|>.le) hp)))
       rw [maple,shuttle,maple]; simp only [Matrix.of_apply,if_neg H,mul_zero,add_zero,abs_zero]; exact funds0 P ha ‹_› hx
    | inr i=> cases i with
       | inr i=> change _*|(0:ℝ)| ≤_;rw [abs_zero,mul_zero]; exact funds0 P ha ‹_› hx -- implicit req
       | inl i=>
          change gained v i.1 (O j)*|runner (straighten S F R) G i j|≤ _; unfold runner; dsimp only [Matrix.of_apply]; split
          · have hz:= (straight_price S a ha.le F R f₀ hp he) (i.1,vac); apply (Finset.single_le_sum (f:=fun t=> gained v i.1 (q t)*|straighten S F R (i.1,vac) t|) (fun i _=> mul_nonneg (gained_pos ..|>.le) (abs_nonneg _)) (Finset.mem_univ j.1)).trans (hz.trans _); exact le_add_of_nonneg_left (add_nonneg hp hk)
          rw [abs_zero, mul_zero]; exact funds0 P ha ‹_› hx
-- general reward point→Syrup via skinny multiplicity after.L. exports one cap integer.Buy slower
omit hp ha hx ht
section
variable {σ ι: Type}[Fintype σ][Fintype ι] (f:σ→Site n)(k:ι→Site n)(V:Matrix σ ι ℝ) {η:ℝ}{N M:ℕ}
noncomputable def shellS (N M :ℕ) (t C E₀:ℝ):= max 1 (t*C*((N+M:ℕ)*countCost E₀))
lemma bookF (he:δ+a+a+b+b ≤ η)(h:0<δ)(ha:0≤a)(hC:0≤B)(hb:0≤b)(hc:0≤C')(hs : ∀ t:ℕ,(1+(t:ℝ))^s≤ B* Real.exp (b*t)) (hp:∀ i j,gained η (f i) (k j)*|V i j| ≤ C')(hN:Multiplicity f N)(hM:Multiplicity k M) : Syrup f k a s V (shellS N M B C' δ):=by
     let S':=(N+M:ℕ); have HH:= le_max_right (1:ℝ) (B*C'*(S'*countCost δ)); have ht(i j): skim f k a s i j*|V i j| ≤ B*C'*Decay δ (f i) (k j):=by
         let S:=separation (f i) (k j); have H:S=S:=rfl; let E₀:= Decay δ (f i) (k j)
         have hx' : skim f k a s i j ≤ B*E₀*gained η (f i) (k j):=by
             have hx:S=S:=rfl
             have hz := hs (2*S); push_cast at hz
             unfold skim Measuring.factor; apply (mul_le_mul_of_nonneg_right hz (Real.exp_pos _|>.le)).trans; rw [mul_assoc B (Real.exp _),mul_assoc B E₀]; unfold E₀ gained Decay; simp_rw [← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hC; change _ + a*(2*S) ≤ -δ*S+η*S; nlinarith only [mul_le_mul_of_nonneg_right he (by positivity : (0:ℝ) ≤ (S:ℝ))]
         refine (mul_le_mul_of_nonneg_right hx' (abs_nonneg _)).trans ?_; rw [mul_assoc _ (gained η (f i) (k j))]; exact (mul_le_mul_of_nonneg_left (hp i j) (mul_nonneg hC (decay_pos ..|>.le))).trans_eq (by ring)
     refine ⟨le_max_left .., fun i=>?_ ,fun j=>?_⟩
     · apply le_trans (Finset.sum_le_sum fun j _=> ht i j); rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left ((Multiplicity.count k hM h (f i)).trans (mul_le_mul_of_nonneg_right (show (M:ℝ) ≤ S' by unfold S'; exact_mod_cast Nat.le_add_left ..) (count_pos h|>.le))) (mul_nonneg hC hc)).trans HH
     refine le_trans (Finset.sum_le_sum fun i _=> ht i j) ?_; rw [← Finset.mul_sum]; simp_rw [decay_comm _ _ (k j)]; exact (mul_le_mul_of_nonneg_left ((Multiplicity.count f hN h (k j)).trans (mul_le_mul_of_nonneg_right (show (N:ℝ) ≤ S' by unfold S'; exact_mod_cast Nat.le_add_right ..) (count_pos h|>.le))) (mul_nonneg hC hc)).trans HH
end
end YM.MSbar.Tramp
