import YM.MSbar.Chord.Thrift
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
variable (e:G.Color)(R:PathData G)(q:Clip)(hp:R.Bounds q a C Λ) (s: Signed) (p:ℕ) (hr:10*(p+4)<n.val) (hE:‖e‖=1)
local notation "J"=> tuner e
local notation "Q"=> url n p a
noncomputable def badge(s:Signed):= (PlaqAxes.transform s).symm pair
lemma badges (p:PlaqAxes)(s:Signed): p.rotate s=pair ↔ p=badge s:=by rw [badge, Equiv.eq_symm_apply]; rfl
lemma hit(p:PlaqAxes)(s:Signed)(e:G.Color): mark p e s= if p=badge s then turned s (badge s) • e else 0:=by unfold mark; by_cases hp:p.rotate s=pair; rw [if_pos hp,(badges p s).1 hp,if_pos rfl]; rw [if_neg hp, if_neg (fun h=>hp ((badges p s).2 h))]
lemma tinted (s:Signed)(p:PlaqAxes): ‖turned s p‖=1:=even_price s ((0:Site ⟨1,Nat.zero_lt_one⟩),p)
include hp hE
private lemma oriented : ∑ i:PlaqAxes, (-2*(q.direct*inner ℝ (mark i e s) (mark i e s)+inner ℝ (setting e R s i) (setting e R s i))) = -2 :=by
    let p:=badge s; let w:= turned s p • e; have he : ‖w‖=1:=by unfold w; rw [norm_smul,tinted,hE,mul_one]
    have hh(i) : setting e R s i = (R.symbol0 i p) • w:=by
        let A(u:ℕ):ℝ := if (R.row i u).2.plaq=p then (R.row i u).1 else 0; unfold setting; simp_rw [hit]; have hh:= hp.symTerms i p; rw [PathData.symbol0,← hh.tsum_smul_const]; refine tsum_congr fun u=>?_ ; split <;> rename_i hu; rfl; rw [smul_zero, zero_smul]
    rw [← mul_sum]; simp_rw [sum_add_distrib,hh]; have hf : ∑ i:PlaqAxes,q.direct* inner ℝ (mark i e s) (mark i e s) = q.direct :=by rw [sum_eq_single_of_mem p (mem_univ _),hit,if_pos rfl, real_inner_self_eq_norm_sq, show ‖turned s (badge s) • e‖=1 from he]; simp; intro i _ hi; rw [hit,if_neg hi];simp
    have ht:= hp.metric p p; simp only [if_true] at ht; rw [hf,show (∑ i:PlaqAxes,inner ℝ ((R.symbol0 i p) • w) ((R.symbol0 i p) • w))= ∑ i:PlaqAxes,(R.symbol0 i p)*(R.symbol0 i p) from (by apply Finset.sum_congr rfl; intro i _; rw [real_inner_self_eq_norm_sq, norm_smul,he,mul_one, Real.norm_eq_abs,sq_abs, pow_two]),ht,mul_one]
    -- edit
include hr
private lemma wrap_one (c:Face (Per n)) : let A:= fun x y=>q.direct*inner ℝ (curlX s c (x:Positions (Primary n G))) (curlX s c y); let F:=fun x y=> inner ℝ (unionC s R c x) (unionC s R c y)
     |gross (fun x y=> A x y+F x y) e- (-2*(q.direct*inner ℝ (mark c.2 e s) (mark c.2 e s)+inner ℝ (setting e R s c.2) (setting e R s c.2)))| ≤ C*C*url n p a:=by
    intro A F; let f:=fun x y:X=>inner ℝ (curlX s c x) (curlX s c y);
    have hh :gross (fun x y=> A x y+ F x y) e= q.direct*gross f e+gross F e:=by unfold gross A; dsimp only; simp only [add_mul,mul_assoc,sum_add_distrib,mul_sum,f]
    have hp :gross f e=-2*inner ℝ (mark c.2 e s) (mark c.2 e s):= waveS s e (stacker G) c c c.1 p hr (by simp) (by simp)
    have he:=wheelPrice e R q ‹R.Bounds ..› s p hr hE.le c; rw [hh,hp]; apply le_trans _ he; apply le_of_eq; apply congr_arg abs; ring
local notation "d!"=>Fintype.card Signed
local notation "x!"=>Fintype.card (Site n)
-- normalized all volume; invocation real S.Probe
omit s
lemma sampled : |grossH (rim (collectT n R q)) e+2| ≤ Fintype.card PlaqAxes * (C*C*url n p a):=by
    let A:= rim (collectT n R q); let F(s:Signed)(c:Face (Per n))(x y:X):= q.direct*inner ℝ (curlX s c x) (curlX s c y)+inner ℝ (unionC s R c x) (unionC s R c y)
    let v(s:Signed)(c:Face (Per n)):= gross (F s c) e; let z(s:Signed)(i:PlaqAxes):= -2*(q.direct*inner ℝ (mark i e s) (mark i e s)+inner ℝ (setting e R s i) (setting e R s i)); let Z:=(x!:ℝ)⁻¹; let d := (d!:ℝ)⁻¹
    have hf(x y:X): A x y=d*∑ s,∑ i,F s i x y:=rates R q hp x y
    have hx : grossH A e= Z*(d*∑ s,∑ i,v s i) :=by
        unfold grossH; simp_rw [hf]; apply congr_arg (Z*·); unfold v; have h(s:Signed): (∑ i,gross (F s i) e)=gross (fun x y=> ∑ i,F s i x y) e:= (pooling ..).symm; simp_rw [h];
        let V(a b:X):= ∑ s:Signed,∑ i:Face (Per n),F s i a b; rw [← show gross V e =_ from pooling e (fun s a b=>∑ i,F s i a b) _]; unfold gross V; dsimp only; simp_rw [mul_assoc,← Finset.mul_sum]
    let T:= C*C*Q; let k:= (Fintype.card PlaqAxes:ℝ); have hc : (x!:ℝ) ≠ 0:=by positivity
    have hd:(d!:ℝ)≠0:=by positivity
    have he(s):∑ i:Face (Per n), z s i.2= -2*x!:=by rw [Fintype.sum_prod_type]; dsimp only; simp_rw [show ∑ a:PlaqAxes,z s a= -2 from oriented e R q hp s hE, sum_const, card_univ,nsmul_eq_mul]; ring
    let H:=∑ s:Signed,∑ i:Face (Per n), (v s i-z s i.2); have hh: Z*(d*H)=grossH A e+2:=by rw [hx]; unfold H; simp_rw [sum_sub_distrib,he,sum_const,card_univ,nsmul_eq_mul]; unfold Z d; field_simp;ring
    change |grossH A e+2|≤k*T; rw [←hh,abs_mul,abs_mul, abs_of_nonneg (by unfold Z; positivity:0 ≤ Z),abs_of_nonneg (by unfold d; positivity:0 ≤ d)]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show |H| ≤ ∑ _:Signed,∑ _:Face (Per n),T from ?_) (by unfold d; positivity)) (by unfold Z; positivity)) ?_
    · unfold H; exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=> (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _=> wrap_one e R q hp i p hr hE j))
    simp_rw [sum_const,card_univ,nsmul_eq_mul]; have hh:Fintype.card (Face (Per n))=x! * Fintype.card PlaqAxes:=Fintype.card_prod ..; rw [hh,Nat.cast_mul]; apply le_of_eq; unfold Z d k; field_simp
end YM.MSbar.Midpoint
