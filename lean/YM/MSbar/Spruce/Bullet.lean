import YM.MSbar.Spruce.Ribbons
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ τ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι]
variable (A:Matrix σ σ ℝ){k n p j h x:ℕ} {a b c W d t r s w t₀ L:ℝ}{m:Side}{M:σ→Site m}
noncomputable def bucks(c t:ℝ)(p:ℕ) := Cash.glow_cost c t p
lemma glowP (h₀:0≤a)(hc:a≤c*L)(ht:0≤t)(hW:t≤w*L)(hz:1≤ L)(p:ℕ): 0≤Cash.glow_cost a t p ∧0≤ Cash.glow_cost c w p∧ Cash.glow_cost a t p ≤ Cash.glow_cost c w p*L^(3+p):=by
    have hL:0<L:=zero_lt_one.trans_le hz; have hk:0≤ w:= nonneg_of_mul_nonneg_left (ht.trans hW) hL; have hh:0 ≤ c:= nonneg_of_mul_nonneg_left (h₀.trans hc) hL
    induction p with
    | zero=>simp only [Cash.glow_cost,one_mul]; exact ⟨zero_le_one,zero_le_one,one_le_pow₀ hz⟩
    | succ p ih=>
                 let g:=Cash.glow_cost a t p; let G:=Cash.glow_cost c w p; let lico:=L^(3+p); have hg':0 ≤ g:=ih.1; have hG:0 ≤ G:=ih.2.1
                 have hΓ:0≤ Cash.glow_cost a t (p+1):=by rw [Cash.glow_cost]; change 0≤g+_+_+_; have hT:=mul_nonneg h₀ hg'; change 0≤g+_*(a*g)+_+_; positivity
                 have hPi:0≤ Cash.glow_cost c w (p+1):=by rw [Cash.glow_cost]; change 0≤G+_*(c*G)+_+_;positivity
                 refine ⟨hΓ,hPi,?_⟩; rw [Cash.glow_cost,Cash.glow_cost]; set J:= lico* L; have hPT:L^(3+(p+1))=J:=by unfold J; rw [← add_assoc,pow_succ] -- J. 
                 have hLi: 1≤lico:=one_le_pow₀ hz; have h':g ≤ G*lico:=ih.2.2; have hQ:=le_mul_of_one_le_right (zero_le_one.trans hLi) hz
                 rw [hPT]; simp only [add_mul _ _ J];
                 change g+(p+1:ℝ)*2*(a*g)+a*t+a^2*t ≤ G*J+_+_+_;
                 refine add_le_add (add_le_add (add_le_add (h'.trans (mul_le_mul_of_nonneg_left hQ hG)) ?_) ?_) ?_
                 · refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hc h' hg' (by positivity)) (by positivity)) ?_; unfold J G; ring_nf; apply le_refl
                 · refine (mul_le_mul hc hW ht (by positivity)).trans ?_; have hL':L^2 ≤ J :=by rw [← hPT]; apply pow_le_pow_right₀ hz;omega
                   exact le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hL' (show 0 ≤ c*w by positivity))
                 refine (mul_le_mul (pow_le_pow_left₀ h₀ hc 2) hW ht (sq_nonneg _)).trans ?_; have hL':L^3≤ J:=by rw [← hPT]; exact pow_le_pow_right₀ hz (by omega)
                 exact le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hL' (show 0 ≤ c^2*w by positivity))
noncomputable def ray (p:ℕ)(q:ℝ):= ((3+p:ℕ):ℝ)*q
variable (v:ι→σ){F: View σ→ℝ}
variable {X Y: View σ}{z:Site m} (hV:Solver v M 0 b c W 0 A)(hw:0≤b)(hv:Injective v)
        (hχ:∀ i:σ,i∉Set.range v → x ≤ separation (M i) z)
        (hq:∀ i:σ,|X i| ≤ a∧|Y i|≤ a)
        (hp:∀ i:σ,|X i-Y i| ≤ d*Eve b z (M i))
include hV hw hv hχ hq hp
variable (ha:0≤a)(hd:0≤d)(hf:FetchD M b t F)
include ha hd hf
noncomputable def toll (p x:ℕ)(b C W d:ℝ):=d+Real.exp (-b*x)*W*(C+stepW (p+1) C)
noncomputable def spend (p:ℕ)(a c t:ℝ):=Cash.glow_cost (1+a+c) (t*(1+(p:ℝ))*(a+stepW (p+1) c)^p) p
local notation "X!"=>hint X (1:Matrix σ σ ℝ) (show Matrix σ σ ℝ from A⁻¹) F
local notation "Y!"=>hint Y (imbed v) ((pinch v A)⁻¹) F
local notation "T₀"=>toll p x b c W d
local notation "W₀"=>spend p a c t
lemma roughM (i:ℕ)(hk:i=p) (L':List σ) (hL:L'.length≤p) :
    |hint X (1:Matrix σ σ ℝ) (show Matrix σ σ ℝ from A⁻¹) F (play L')- hint Y (imbed v) ((pinch v A)⁻¹) F (play L')| ≤ (T₀*W₀)* spread M {z} (ray p b) 0 L':=by
    let s₀:=spread M {z} b 0 L'; have hs:1≤ s₀:=w_start hw 0 _; let J:=stepW (p+1) c; have hX:=hV.bsize
    have hz (j:σ)(hp:j ∈ L'.toFinset): Eve b z (M j) ≤ s₀:=by have he:=radius_go M (i:=j) (List.mem_toFinset.mp hp) (mem_singleton_self z) hw 0; simpa only [liftW,Eve,s₀,pow_zero,one_mul] using he
    have hV' := Solver.pays_cov (p:=p) v hv hV hχ hw hz hq hp hf ha hs hd
    let V:=s₀+a+c; let g:= t*(1+(p:ℝ)*s₀)*(a+J)^p; have hτ:g*1=g:=mul_one _; have hZ:0≤T₀:= hV'.chances.soft; have hg:=hV'.budgets
    apply (hV'.blade L' (Finset.Subset.refl _) hL|>.2.2).trans; change T₀* Cash.glow_cost V g p ≤ _; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hZ
    have hR :s₀^(3+p)=spread M {z} (ray p b) 0 L':=by unfold s₀ Whisk.spread liftW ray; rw [pow_zero,one_mul,one_mul,← Real.exp_nat_mul,mul_assoc]
    rw [←hR]; apply (glowP (show 0≤ V from by unfold V; linarith) _ (show 0≤ g from hg) _ hs p|>.2.2) -- maybe syntax
    · unfold V; linarith only [hs,mul_nonneg (sub_nonneg.mpr hs) ha, mul_nonneg (sub_nonneg.mpr hs) hX]
    unfold g; let lico:=t; have hJ:0≤ J:=by unfold J stepW; positivity
    change _≤t*(1+(p:ℝ))* (a+J)^p*s₀; rw [mul_right_comm (t*(1+↑p)), mul_assoc t (1+↑p:ℝ)]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hf.nonnegative) (by positivity); linarith only [hs]
lemma polite (u':Pot σ)(he: u'.totalDegree≤p)(hF:Vault M {z} (ray p b) 0 p 0 u' s):
      |hint X 1 (show Matrix σ σ ℝ from A⁻¹) F u'-hint Y (imbed v) ((pinch v A)⁻¹) F u'| ≤ (p+1:ℕ)*((T₀*W₀)*s):=by
     obtain ⟨α,hα⟩:= pint (1:Matrix σ σ ℝ) X hV.bids.inv hf.whole
     obtain ⟨R,hR⟩:= pint (imbed v) Y (show Matrix.PosDef ((pinch v A)⁻¹) from (hV.bids.submatrix hv).inv) hf.whole
     let K:= T₀*W₀; have hPi:= roughM A v hV hw hv hχ hq hp ha hd hf p rfl [] (by simp); have hV':0≤K:= nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hPi) (effect ..)
     let G:=α-R; have hh(i): G i= X! i-Y! i:=by change α i-R i= _; rw [hα,hR]; -- transparency
     rw [←hh u']; nth_rw 1 [← Spruce.tape u' p he]; unfold ropes; rw [map_sum]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>K*s) (fun j hj=>?_)).trans_eq ?_)
     · unfold scores; rw [map_smul]; -- scores
       have hz:j≤p:=Nat.le_of_lt_succ (mem_range.mp hj); have he : |G (dart j u')|≤ K*s:=by
           rw [dart,show G (Yarn j _) = _ from Whisk.spun G.toAddMonoidHom j (fun L:List σ=> Whisk.read 0 L u' • play L)]; apply (polished ..).trans; refine le_trans (b:=K*lump M {z} (ray p b) 0 j 0 u') ?_ (mul_le_mul_of_nonneg_left (hF.2 j hz) hV'); unfold lump; rw [←sheen]; refine shiny j fun L hl=>?_ ; change |G (_ • play L)|≤ _; rw [map_smul,smul_eq_mul,abs_mul,hh]; exact (mul_le_mul_of_nonneg_left (roughM A v hV hw hv hχ hq hp ha hd hf p rfl L (hl.trans_le hz)) (abs_nonneg _)).trans_eq (by unfold rate K; ring)
       rw [smul_eq_mul,abs_mul]; apply le_trans (mul_le_mul_of_nonneg_left he (abs_nonneg _)); apply mul_le_of_le_one_left (mul_nonneg hV' hF.1); rw [abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos j))
     rw [sum_const,nsmul_eq_mul,card_range]
end YM.MSbar.Spruce
