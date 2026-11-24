import YM.MSbar.Chord.Tones
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
local notation "M"=> Moment Q
variable (x:Edge (Site n))(c:Axis) (u v:G.Color) (h:Ribbon Q)(hQ:Weigh Q Z) (hu:‖u‖=1)(hv:‖v‖=1)
include h
lemma turning (s:Signed)(t:S₀)(L: List Axis) : M (sendEdge s t x) (s.perm c) u v (L.map s.perm)= sign s x.2*sign s c * ∑ i:Site n, cell Q x (i,c) u v*mold (L.map s.perm) (sendEdge s t x) (sendEdge s t (i,c)) :=by
    let H:=sendEdge s t; let p(z:S₀):= (H (z,c)).1; have he(z:S₀):H (z,c)=(p z,s.perm c):=Prod.ext rfl (foot ..); have hp:Injective p:=fun i j h=> by
        have ht:= (he i).trans ((Prod.ext (x:=(p i,s.perm c)) (y:=(p j,s.perm c)) h rfl).trans (he j).symm)
        exact (Prod.mk.inj ((sendEdge_injective s t) ht)).1
    let e:= Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp); unfold Moment; rw [←Equiv.sum_comp e, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); change cell Q (H x) (p i,s.perm c) u v*mold _ _ _=_; rw [show e i=p i from rfl,← he i]; rw [show cell Q (H x) _ u v=_ from flips Q h x (i,c) s t u v]; rw [mul_assoc]
omit h
lemma P_pad (a:S₀)(b:S₀)(i j:ℕ)(he:i≤j):beadPad a b i≤beadPad a b j:=pow_le_pow_right₀ (by simp) he
lemma glass(s:Signed)(j:Axis):|sign s j|=1:=by unfold sign; split <;> norm_num
lemma sharp(s:Signed)(l:List Axis):|bill s l|=1:=by induction l with
    | nil=>simp [bill]
    | cons i l ih=> rw [show bill s _= sign s i*bill s l by simp [bill],abs_mul,glass,ih,one_mul]
include h hQ hu hv
lemma axPrice (s:Signed)(b:S₀) (l:List Axis)(hp:l.length≤2):
   |M (sendEdge s b x) (s.perm c) u v (l.map s.perm)- sign s x.2*sign s c*(bill s l*M x c u v l)| ≤ 17*tumbler n Z :=by
    rw [turning x c u v h s b,← mul_sub, abs_mul,abs_mul,glass,glass,one_mul,one_mul]; let f(i:S₀):=cell Q x (i,c) u v; let A:=sendEdge s b x; let p(i:S₀):= sendEdge s b (i,c); let g(i):=mold (l.map s.perm) A (p i)-bill s l*mold l x (i,c); let Y(i:S₀):=f i*g i
    unfold Moment; rw [Finset.mul_sum,← Finset.sum_sub_distrib];
    refine le_trans (le_of_eq (congr_arg _ (Finset.sum_congr (g:=Y) rfl (fun i _=>?_)))) (values x c u v g hQ hu hv (C:=17) (by norm_num) (fun i hk=>?_)); swap
    · have hv:¬ 100*(separation i x.1+1)<n.val:=by
        intro hx; apply hk; apply sub_eq_zero.mpr; have hz(j:Axis) : middle A (p i) (s.perm j)= sign s j*middle x (i,c) j:=pulse s b x (i,c) j hx; unfold mold bill; rw [List.map_map]; have hh(P:List Axis):(P.map (middle A (p i) ∘ ⇑s.perm)).prod= (P.map (sign s)).prod*(P.map (middle x (i,c))).prod:=by
             induction P with 
             | nil=> simp
             | cons k l IH=> simp only [List.map_cons,List.prod_cons,hz,Function.comp_apply,IH]; ring -- simp after comp
        exact hh l
      refine ⟨Nat.le_of_not_gt hv,?_⟩; unfold g; apply (abs_sub ..).trans; rw [abs_mul,sharp,one_mul]; have hz:= castA l x (i,c); refine (add_le_add ((castA _ _ _).trans ((pads x s b (i,c) _ (by simpa using hp)).trans (mul_le_mul_of_nonneg_left (P_pad x.1 i 2 3 (by omega)) (by norm_num)))) (hz.trans (P_pad x.1 i _ 3 (by omega)))).trans_eq ?_; ring
    unfold Y f g A p; ring
end YM.MSbar.Midpoint
