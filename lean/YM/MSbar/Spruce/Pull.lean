import YM.MSbar.Spruce.Bullet
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Analysis
variable {ι σ τ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι][Fintype τ][DecidableEq τ]
variable (q :View σ)(u:ι→σ)(L:View ι→L[ℝ] View σ)
variable {j p n m:ℕ}{c:Side}{M:σ→ Site c}{z:Site c}{r t a b:ℝ}{w:View ι}
local notation "π"=> Positions
lemma imbed_tone (i:ι) : Kelvin.imbed u *ᵥ bolt i = Uniform.bolt (u i):=by
    ext j; simp [bolt,mulVec,Pi.single_apply,dotProduct,imbed,ite_mul,eq_comm]
noncomputable def afford (u:ι→ σ):View ι→L[ℝ]View σ:= LinearMap.toContinuousLinearMap (Matrix.toLin' (imbed u))
lemma glide (p:ℕ)(T:List ι)(he:T.length≤ p) (hu:∀ i:ι,L (bolt i)=bolt (u i))(F:View σ→ ℝ)(hF:ContDiff ℝ p F)(x:View ι):
      glance (fun y=> F (q+L y)) T x=glance F (T.map u) (q+L x):=by
    induction T generalizing p F with
    | nil=> rfl
    | cons i T ih=>
         let f(y:View ι) := q+L y; have hs : Differentiable ℝ F:=hF.differentiable (Nat.cast_ne_zero.mpr (show p≠0 by rw [List.length_cons] at he; omega)); let G:=Analysis.D (Pi.single (u i) 1) F
         have hp : Analysis.D (Pi.single i (1:ℝ)) (F ∘ f)= G ∘ f:=by
              ext a; unfold Analysis.D; rw [fderiv_comp a (hs (f a)) (by unfold f; fun_prop), show fderiv ℝ f a=L from ((L.hasFDerivAt.const_add q).fderiv)]; rw [ContinuousLinearMap.comp_apply]; rw [show (Pi.single i (1:ℝ): View ι)=Uniform.bolt i from (by ext v; simp [bolt,Pi.single_apply])]; rw [hu]; unfold G Analysis.D; dsimp only [Function.comp_apply]; rw [show Uniform.bolt (u i)= (Pi.single (u i) 1:View σ) from (by ext v; simp [bolt,Pi.single_apply])]
         change glance (Analysis.D (Pi.single i (1:ℝ)) (F ∘f)) T x=_; rw [hp]; rw [List.map_cons,glance]; convert! ih T.length le_rfl G ?_ using 1
         apply contDiff_iff_contDiffAt.mpr; intro y; exact dSmooth (hF.contDiffAt) _ (by exact_mod_cast he)
lemma subtot (u:ι→σ)(h:Injective u)(f:σ→ℝ)(he:∀ i,0 ≤ f i): ∑ i,f (u i)≤ ∑ i, f i:=by
    let S:= univ.image u; rw [show ∑ i,f (u i)= ∑ i∈S,f i from (sum_image (fun _ _ _ _ hp=> h hp)).symm]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> he i
lemma fetch (b:ℝ)(hu:Injective u)(hV:∀ i,L (bolt i)=bolt (u i))(F:View σ→ ℝ)(hf:FetchD M b t F):FetchD (M ∘ u) b t (fun y=> F (q+L y)):=by
    let g:=fun y=> F (q+L y); have h:= hf.whole; obtain ⟨c,hc⟩:=h.whole; have hK:ContDiff ℝ (↑(2:ℕ)) F:= contDiff_iff_contDiffAt.mpr hf.smooth
    have hg : ContDiff ℝ (↑(2:ℕ)) g:=hK.comp (contDiff_const.add L.contDiff); have he(i:ι)(x:View ι):|glance g [i] x| ≤ t:=by unfold g; rw [glide q u L 2 [i] (by simp) hV F hK]; exact hf.tilt _ _
    refine ⟨⟨hg.of_le (by norm_num),⟨c,fun x=>hc _⟩,fun i=>⟨t,he i⟩⟩,fun i=>?_,hf.nonnegative,he,fun i=>?_⟩ -- hp
    · exact hg.contDiffAt
    obtain ⟨h,H,ht⟩:=hf.rises (u i); refine ⟨h ∘ u,fun x j=> ?_,?_⟩
    · rw [glide q u L 2 [i,j] (by simp) hV F hK]; exact H _ _
    exact (subtot u hu (fun j=> h j * Eve b (M (u i)) (M j)) (fun j => mul_nonneg ((abs_nonneg _).trans (H 0 j)) (Real.exp_pos _|>.le))).trans ht -- wrong input
noncomputable def clasp (q:View σ)(P:Matrix σ ι ℝ): Pot σ→ₐ[ℝ] Pot ι := aeval fun i=> C (q i)+ Rolling.rail P (X i)
lemma value (x:View ι) (f:Pot σ): eval x (clasp q (imbed u) f)=eval (q + (afford u) x) f:=by -- undeclared l
    let L:=imbed u; induction f using MvPolynomial.induction_on with
    | C v=>simp [clasp]
    | add f g hf hg=> rw [_root_.map_add,_root_.map_add,_root_.map_add,hf,hg]
    | mul_X p i ih=> rw [_root_.map_mul,_root_.map_mul,ih,_root_.map_mul,MvPolynomial.eval_X,clasp,MvPolynomial.aeval_X,_root_.map_add,MvPolynomial.eval_C,show eval x (Rolling.rail L _)=_ from (show eval x (Rolling.rail _ (X i))= _ from congr_fun (clearL L x) (X i)),MvPolynomial.eval_X]; rfl
lemma gradeP (f:Pot σ)(p:Matrix σ ι ℝ): (clasp q p f).totalDegree ≤ f.totalDegree:=by
    let Z:=clasp q p; have h(i): (Z (X i)).totalDegree ≤ 1:=by unfold Z clasp; rw [aeval_X]; exact (totalDegree_add ..).trans (max_le (by rw [totalDegree_C];omega) ((clearD ..).trans (le_of_eq (totalDegree_X ..))))
    nth_rw 1 [MvPolynomial.as_sum f]; rw [_root_.map_sum]; apply totalDegree_finsetSum_le; intro i hi; rw [monomial_eq]; change (Z _).totalDegree ≤ _; rw [_root_.map_mul,_root_.map_finsuppProd]; refine (totalDegree_mul ..).trans ?_; simp only [Finsupp.prod]; simp only [Z,clasp,MvPolynomial.aeval_C]
    rw [show algebraMap ℝ (Pot ι)= C from rfl,totalDegree_C,Nat.zero_add]; refine (totalDegree_finsetProd ..).trans (le_trans ?_ (le_totalDegree hi)) -- fix
    apply Finset.sum_le_sum; intro j hj; change totalDegree (Z (_ ^ _))≤ i j; rw [_root_.map_pow]; exact (totalDegree_pow ..).trans ((Nat.mul_le_mul_left _ (h _)|>.trans (by omega)))
lemma cheer (u:ι→σ)(f:List σ→ ℝ)(he:∀ l,0≤ f l)(hu:Injective u)(m:ℕ): Yarn m (fun l:List ι=>f (l.map u)) ≤ Yarn m f := by induction m generalizing f with
    | zero=> exact le_rfl
    | succ m ih=> rw [twilled, twilled]; refine (sum_le_sum (fun i _=>?_)).trans (subtot u hu (fun j:σ=> Yarn m (fun l=> f (j::l))) (fun i=>luster m (fun l h=>he _))); exact ih (fun l=> f (u i::l)) (fun i=>he _)
lemma crossP (hu:Injective u)(ha:0≤a)(f:Pot σ)(hF:Vault M {z} a p m q f t):Vault (M ∘ u) {z} a p m 0 (clasp q (imbed u) f) t:=by -- p binder
    let L:= imbed u; let w:=clasp q L f; let p'(x:View σ):=eval x f; have he(x:View ι): eval x w=p' (q + (afford u) x):=value q u x f -- l binder
    let H := rate M {z} a p q f; let g := rate (M ∘ u) {z} a p 0 w; have hL(l:List ι):g l= H (l.map u):=by
        have hh: Whisk.zone (M∘u) {z} l=Whisk.zone M {z} (l.map u):=by unfold Whisk.zone; rw [List.map_map]
        have hp : Whisk.read 0 l w=Whisk.read q (l.map u) f:=by
             rw [←glance_jet]; simp_rw [he]; unfold p'; rw [glide q u (afford u) l.length _ le_rfl (fun i=> ?_) _ (vent f|>.of_le le_top),_root_.map_zero,add_zero,glance_jet]; exact imbed_tone u i
        unfold g H Whisk.rate Whisk.spread; rw [hh,hp]
    have hL' : g=(fun l=>H (l.map u)):=funext hL; refine ⟨hF.1,fun j hj=>?_⟩; change Yarn j g≤ t; rw [hL']; refine le_trans (cheer u H (fun l=> ?_) hu j) (hF.2 j hj); exact mul_nonneg (wpos ..|>.le) (abs_nonneg _)
end YM.MSbar.Spruce
