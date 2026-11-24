import YM.MSbar.Lodge.Clamp
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
open Set Metric
local notation "Π"=>Positions σ
variable {g:ℝ→ℝ}{w B C:ℝ}{q k m:ℕ}(h:Hat k w B g) {F:Positions σ→ℝ}
local notation "Ψ"=> iteratedFDeriv ℝ
variable (hs:1 ≤B) {x:Positions σ}{i: σ} (l:List σ)
include h
lemma road(hq:l.length+1≤k): |buoy (fun x:Positions σ=>deriv g (x i)) x l|≤ B:=by
   let G:= deriv g; let j:= fderiv ℝ g; let p:= l.length; let L:Positions σ→L[ℝ]ℝ:=ContinuousLinearMap.proj i; let H:= iteratedFDeriv ℝ p G (x i); let t:=x i; let V:= ContinuousLinearMap.apply ℝ ℝ (1:ℝ)
   have hl: ContDiffAt ℝ (↑p) j t:=h.smooth.contDiffAt.fderiv_right (by exact_mod_cast hq); have hh: ContDiffAt ℝ (↑p) G t:= V.contDiff.contDiffAt.comp t hl
   have hv:‖V‖ ≤1:=by apply V.opNorm_le_bound zero_le_one; intro f; rw [one_mul]; exact (f.le_opNorm 1).trans_eq (by rw [norm_one,mul_one])
   have hx:‖H‖ ≤ B:=by
       have he: G= V ∘ j:=rfl; unfold H; rw [he]; apply (ContinuousLinearMap.norm_iteratedFDeriv_comp_left V (n:=p) hl le_rfl).trans; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) hv); unfold j; rw [norm_iteratedFDeriv_fderiv]; exact h.head _ _ hq
   unfold buoy; change |roc (G ∘ L) (l.map (@bolt σ)) x|≤ _; let f:=(List.map L (l.map (@bolt σ)))
   have hf: f.length=p:=by unfold f p; simp only [List.length_map]
   rw [toe L p (l.map bolt) hh (by unfold p; simp only [List.length_map,le_refl])]; change |roc G f t| ≤ B; rw [rod p _ _ hh hf.le]
   refine (ContinuousMultilinearMap.le_opNorm (Ψ f.length G t) _).trans ?_; refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) (by rw [hf]; exact hx)
   apply Finset.prod_le_one; exact fun _ _=> norm_nonneg _
   intro v _; obtain ⟨m,hm,hM⟩:= List.mem_map.mp (show f.get v∈f from List.get_mem ..); obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (show m∈ l.map (@bolt σ) from hm); rw [← hM, ← norm_bolt a]; exact norm_le_pi_norm (bolt a) i
variable (hf :∀ x:Positions σ,ContDiffAt ℝ k F (Clamp g x))(x: Positions σ) (i:σ)
local notation "W"=>F ∘ Clamp g
include hf hs
-- uniform coarse per tuple λ=Π.L
noncomputable def expense (p:ℕ)(B:ℝ):= (2^p*B)^(p+1)
lemma work (v:σ)(T:List σ) (he:T.length=m) (hk:m+1≤k)(hT:∀ l:List σ,l≠[]→l.length≤ k → |buoy F (Clamp g x) l| ≤ C)(hc:0 ≤ C) : |buoy (F∘ Clamp g) x (v::T)| ≤ expense m B * C :=by
   induction m using Nat.strong_induction_on generalizing v T k F with
   | h m ih=>
      let V:=@Clamp σ g; let Y(y:Π):=buoy F y [v]; let f(y:Π):= deriv g (y v); have hF(m')(hh:m'+1 ≤ k)(x:Π):ContDiffAt ℝ (↑(m':ℕ)) Y (V x):=Lis.smooth k _ _ (hf x) (by simp only [List.length_map,List.length_cons,List.length_nil]; omega)
      have hh:ContDiffAt ℝ m f x:=by
          let L:= fderiv ℝ g; have hp :ContDiffAt ℝ m L (x v):= h.smooth.contDiffAt.fderiv_right (by exact_mod_cast hk); refine (show ContDiffAt ℝ m (deriv g) (x v) from ((ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).contDiff.contDiffAt.comp _ hp)).comp x (contDiffAt_apply ℝ ℝ v _)
      have hF' : ContDiffAt ℝ m (Y ∘ V) x:= (hF _ hk x).comp _ ((hut h|>.contDiffAt).of_le (by exact_mod_cast (show m≤ k from by omega)))
      rw [recur h hf x v T (by omega),paisley m f (Y ∘ V) x T hh hF' he.le,he]; let C':=((2:ℝ)^m*B)^m*C
      have ht: 1≤(2:ℝ)^m*B:=one_le_mul_of_one_le_of_one_le (by apply one_le_pow₀; norm_num) hs
      calc
        _ ≤ Yarn m (fun _ : List Bool=> B*C') :=by refine (polished ..).trans (shiny _ ?_); intro i hx; have hz(b): (takeout b i T).length≤ m :=(sunset _ _ _ (by omega)).trans_le ((part_le ..).trans_eq hx); rw [abs_mul]; refine mul_le_mul (road h _ (le_trans (Nat.add_le_add_right (hz true) 1) hk)) ?_ (abs_nonneg _) (zero_le_one.trans hs)
                                                   obtain hd|⟨b,L,hL⟩: takeout false i T=[]∨∃ b L,takeout false i T=b::L:=by cases h:takeout false i T <;> simp <;> try grind -- need cons
                                                   · rw [hd]; change |buoy F (Clamp g x) [v]| ≤ _; exact (hT _ (by simp) (by simp; omega)).trans (le_mul_of_one_le_left hc (one_le_pow₀ ht))
                                                   have hb:Hat m w B g:=⟨h.value,h.honest,h.smooth.of_le (by exact_mod_cast (show m≤ k from by omega)),fun x i hi=> h.head _ _ (by omega)⟩
                                                   have he':L.length < m:=by have he':= hz false; rw [hL,List.length_cons] at he'; omega
                                                   have hG(l:List σ)(hl:l.length≤ m): buoy Y (V x) l= buoy F (V x) (v::l):= (takeG k (hf x) (l.map (@Uniform.bolt σ)) (bolt v) (by rw [List.length_map]; omega)).symm
                                                   rw [hL]; apply (ih L.length he' hb (hF _ hk) b L rfl (by omega) (fun l _ hl=>by rw [show buoy Y _ _= _ from hG l hl]; exact hT _ (by simp) (by rw [List.length_cons]; omega))).trans; apply mul_le_mul_of_nonneg_right _ hc; unfold expense; apply le_trans (b:=((2:ℝ)^m*B)^(L.length+1)) (pow_le_pow_left₀ _ _ _); · exact pow_le_pow_right₀ ht (by omega)
                                                   · have hx:=zero_lt_one.trans_le hs; positivity
                                                   exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two he'.le) (zero_le_one.trans hs)
        _ = _:=by have hp(j:ℕ): Yarn j (fun _ : List Bool=> B*C')=2^j*(B*C'):=by induction j with |zero=>change B*C'=_;rw [pow_zero,one_mul]|succ i ih=>rw [twilled];simp_rw [ih];rw [sum_const,nsmul_eq_mul];simp; ring -- grouping
                  rw [hp]; unfold C' expense; ring
end YM.MSbar.Lodge
