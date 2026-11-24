import YM.MSbar.Chord.Ideal
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{a D C Λ:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> (n.val:ℝ)
local notation "Θ"=>G.Color
local notation "H"=> tint G (Exterior.Body 1 n)
local notation "ι"=>G.ColorIndex
variable (e:G.Color)(R:PathData G)(q:Clip)(hp:R.Bounds q a C Λ) (s: Signed) (p:ℕ) (hr:10*(p+4)<n.val) (hE:‖e‖=1)
local notation "M"=> tuner e
include hp hE
noncomputable def marker (s:Signed)(i:Atom G 2)(v:G.Color):= rows i (mark (i.leg 0|>.plaq) v s) (mark (i.leg 1|>.plaq) v s)
lemma sunnyB(s:Signed): ∑' i:ℕ,marker s (R.loop i) e=0 ∧ Summable (fun i:ℕ=>marker s (R.loop i) e):=by
    let l:=badge s; let w:=turned s l • e; let p(i):=R.loop i; let M'(i)(j:Fin 2→ι):=R.loop_coeff (fun _=>l) j i
    let F(i:ℕ)(j:Fin 2→ι):= M' i j *w (j 0)*w (j 1)
    have hu (i:ℕ) : marker s (R.loop i) e=∑ j,F i j:=by
         unfold marker; rw [hit,hit]; change ∑ j,(p i).coeff j * (_) * _= _; refine Finset.sum_congr rfl (fun j _=>?_); by_cases hh:(p i|>.leg 0).plaq=l ∧ (p i|>.leg 1).plaq=l
         · rw [if_pos hh.1,if_pos hh.2]; unfold F M' PathData.loop_coeff; rw [if_pos ?_]; ext1 j; fin_cases j; exact hh.1; exact hh.2
         have he:M' i j=0:= if_neg (fun h=>hh ⟨congr_fun h 0, congr_fun h 1⟩); unfold F; rw [he,zero_mul,zero_mul]; rcases (not_and_or.mp hh) with h|h
         · rw [if_neg h]; simp
         rw [if_neg h];simp
    have he(j): HasSum (fun i=> F i j) 0:=by
        have he': HasSum (fun i=> M' i j) 0:=by rw [← (hp.loop_normal (fun _=>l) j).1]; exact (hp.loopTerms _ j).1.hasSum
        have h := (he'.mul_right (w (j 0))).mul_right (w (j 1)); simp only [zero_mul] at h; exact h
    simp_rw [hu]; refine ⟨?_,summable_sum fun j _ => (he j).summable⟩; rw [Summable.tsum_finsetSum (fun j _=> (he j).summable)]; exact sum_eq_zero fun i _=> (he i).tsum_eq
include hr
lemma lune (x:S₀): |gross (fun a b:X=>∑' k, readG (R.loop k) s x a b) e| ≤ Λ * url n p a:=by
    let G'(k:ℕ):=gross (readG (R.loop k) s x) e; obtain ⟨hA,hS⟩:= mosaic e (fun k=> readG (R.loop k) s x) (fun i j=> sunny R q hp s x _ _)
    let f(k:ℕ):= -2 * marker s (R.loop k) e; obtain ⟨he,hV⟩:= sunnyB e R q hp hE s
    have hz:∑' i, f i=0:=by unfold f; rw [tsum_mul_left, he,mul_zero]
    have hK:Summable f:=hV.mul_left _
    have h(i:ℕ): |G' i-f i|≤ (R.loop i).budget a * url n p a :=by
         let A:= R.loop i; have hh(i:Fin 2) : (A.leg i).length ≤ A.length:=single_le_sum (f:=fun i=> (A.leg i).length) (fun _ _=> Nat.zero_le _) (mem_univ _); have ht := routeS (G:=G) e x s (rows A) p hr hE.le hp.width (show 0 ≤ A.magnitude from sum_nonneg (fun _ _=>abs_nonneg _)) (price_row A) (A.leg 0) (A.leg 1) A.length (hh _) (hh _); exact ht
    rw [hS,← sub_zero (∑' i:ℕ,gross (readG (R.loop i) s x) e),← hz, ← Summable.tsum_sub hA hK]; refine (norm_tsum_le_tsum_norm ((hA.sub hK).norm)).trans (((hA.sub hK).norm.tsum_le_tsum h (hp.two.2.1.mul_right _)).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hp.two.2.2 (spreadR ..)
local notation "i!"=> (Fintype.card (Site n):ℝ)
omit s
omit hp hE hr in
lemma swing (x y: Site n)(d:Axis): coord x y d^2= coord y x d^2:=by
    have h : |coord x y d|=|coord y x d|:=by unfold coord lift; rw [show x-y=-(y-x) from (neg_sub ..).symm]; change |(( _ :ℤ):ℝ)| = |((ZMod.valMinAbs (-((y-x) d)):ℤ):ℝ)|; exact_mod_cast (by rw [← Int.natCast_natAbs,← Int.natCast_natAbs,ZMod.natAbs_valMinAbs_neg] : |ZMod.valMinAbs ((y-x) d)| = |ZMod.valMinAbs (-((y-x) d))|)
    rw [← sq_abs, h, sq_abs]
lemma elo : |grossH (rim (liveLoop n R)) e| ≤ 2*Λ *url n p a:=by
    let f(s:Signed)(x:Site n):=gross (fun a b:X=>∑' k, readG (R.loop k) s x a b) e; let Y:=era n R; let A:=rim (liveLoop n R); let d:= (Fintype.card Signed:ℝ); let Z:=d⁻¹
    have hh:gross Y e= Z*∑ s,∑ i,f s i:=by
       let F(s:Signed) (i:Site n)(a b:X):=∑' k, readG (R.loop k) s i a b; simp_rw [show f=(fun s i=> gross (F s i) e) from rfl]; rw [show (∑ s,∑ i, gross (F s i) e)= gross (fun a b=>∑ s:Signed,∑ i:Site n,F s i a b) e from ?_]; swap; · rw [pooling]; apply Finset.sum_congr rfl; intro i _; rw [pooling] -- unif
       unfold gross Y era Patch.average; dsimp only; simp_rw [mul_assoc, ← Finset.mul_sum]; rfl
    have hv:gross (fun x y=>A x y) e=2*gross Y e:=by
       rw [two_mul]; unfold gross; simp_rw [show ∀ x y,A x y=Y x y + Y y x from (fun x y=> eraP R q hp x y|>.2),add_mul,sum_add_distrib]; apply congr_arg; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; exact sum_congr rfl (fun j _=>by rw [swing j i]) -- dsimp too much
    have hn:0 < i! :=by positivity
    have hd:0<d:= Nat.cast_pos.mpr Fintype.card_pos
    let k:= Λ *url n p a; have hG:|∑ s:Signed,∑ i:S₀,f s i| ≤ d*(i! *k):=by
        apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum (g:=fun s=> ∑ i:S₀,k) (fun s _=> (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=> lune e R q hp s p hr hE i)))).trans_eq; rw [sum_const]; simp [d]
    unfold grossH; rw [hv,hh,abs_mul,abs_mul,abs_mul,abs_of_pos (show (2:ℝ)>0 by norm_num),abs_of_nonneg (show 0≤ Z from inv_nonneg.mpr hd.le),abs_of_nonneg (show 0 ≤ (i!)⁻¹ from inv_nonneg.mpr hn.le)]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (show 0 ≤ Z from (inv_pos.mpr hd).le)) zero_le_two) (inv_pos.mpr hn).le) _; unfold Z k; apply le_of_eq; field_simp
end YM.MSbar.Midpoint
