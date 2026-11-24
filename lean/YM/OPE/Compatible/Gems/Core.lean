import YM.OPE.Compatible.Gems.Bali
/-! # Projection supply uniform precision payments, no Card.X W. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset Matrix
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav
variable {X Y J:Type}{t r s:ℝ}{i:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
variable (A:Law X)
section
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y](S:X→ₗ[ℝ] Y)(h:Surjective S)
local notation "L"=>claspR A S h
local notation "H!"=> chiselR A S h
lemma scene : Swear A S L:= ⟨drapeB A S h, fun x hx i=>by rw [Chwist,hx,_root_.map_zero]⟩
lemma chestH (x y:Y): A.P (L x) (L y)= (H!).P x y:= by rw [Chwist A S h,drapeB]; rfl
lemma Pane (x:X): (H!).P (S x) (S x) ≤ A.P x x:=by
       let p:=claspR A S h (S x); let g:=x-p; have he:(H!).P (S x) (S x)= A.P p p:=(chestH A S h ..).symm; have hp: S g=0:=Swear.rot A S L (scene A S h) x; have hg: A.P p g=0:= (scene A S h).rich g hp _; have hz : A.P x x=A.P p p+A.P g g:=by
            nth_rw 1 2 [show x=p+g from (add_sub_cancel p x).symm]; rw [A.P.map_add,LinearMap.add_apply,(A.P p).map_add,(A.P g).map_add,A.turns g p,hg,add_zero,zero_add]
       have hP:0 ≤ A.P g g:=by obtain ⟨u,hu,H⟩:=A.slope; linarith only [mul_nonneg hu.le (sq_nonneg ‖g‖), H g]
       rw [hz,he]; linarith
lemma Chide (p:Module.Dual ℝ X):
     let x:= S (A.inverse p); (p ∘ₗ L)=(H!).P x∧ A.wick (p.comp ((L).comp S)) (p.comp ((L).comp S))=(H!).P x x:=by
       intro x; have hv:(p ∘ₗ L)=(H!).P x:=by
             apply LinearMap.ext; intro i; rw [(H!).turns]; change p (L i)=_; calc
                  _ = A.P (A.inverse p) (L i):= by rw [Law.applies]
                  _ = (H!).P i x:=by rw [A.turns,Chwist]; rfl
       refine ⟨hv,?_⟩; rw [show p.comp ((L).comp S)=(H!).P x ∘ₗ S from by rw [← hv];rfl]; rw [←tunesB A S h]; unfold Law.wick; rw [(H!).solves]
end
section
variable [Fintype J][DecidableEq J]
local notation "F"=> (J→ℝ)
variable (S:X→ₗ[ℝ] (J→ℝ))(h:Surjective S)
local notation "L"=>claspR A S h
local notation "H!"=> chiselR A S h
-- hx existence of budget caps on sparse stencil
variable (ht:∀ i:J,∃ p,S p=Pi.single i 1 ∧ A.P p p ≤t)
include ht
lemma scent (i j:J) : |(H!).P (Pi.single i 1) (Pi.single j 1)| ≤ t:=by
       let p:=chiselR A S h; let u:F:= Pi.single i 1; let v:F:= Pi.single j 1; obtain ⟨r,s,hp⟩:=ht i; obtain ⟨w,a,hq⟩:=ht j; have hu:p.P u u≤t:= (show S r=u from s) ▸ ((Pane A S h r).trans hp); have hv:p.P v v≤ t:= (show S w=v from a) ▸ ((Pane A S h w).trans hq); have he(x:F):0 ≤p.P x x:=by obtain ⟨q,h,H⟩:=p.slope; linarith only [mul_nonneg h.le (sq_nonneg ‖x‖), H x]
       have h:=he (u+v); have hz:=he (u-v); rw [p.P.map_add,LinearMap.add_apply,(p.P u).map_add,(p.P v).map_add,p.turns v u] at h; rw[p.P.map_sub,LinearMap.sub_apply,(p.P u).map_sub,(p.P v).map_sub,p.turns v u] at hz; change |p.P u v|≤ t; rw[abs_le]; constructor<;> linarith only [h,hz,hu,hv]
lemma vein (p:Module.Dual ℝ X)(hx:∀ i:J,‖A.wick p ((LinearMap.proj i) ∘ₗ S)‖≤ s) (hs:0≤ s)(_hp:0 ≤t):
    A.wick (p.comp ((L).comp S)) (p.comp ((L).comp S))≤(Fintype.card J:ℝ)^ (2:ℕ)*t*s^ (2:ℕ):=by
          let x:= S (A.inverse p); let g(i:J):F:= Pi.single i 1; let T:=H!; have he(i:J) : ‖x i‖≤ s:=hx i; rw [(Chide A S h p).2]; change T.P x x ≤ _; let n:ℝ:= ↑(Fintype.card J)
          rw [show x=∑ i,x i • g i from funext fun i=>by simp [Finset.sum_apply,Pi.single_apply,g],_root_.map_sum T.P,LinearMap.sum_apply]; refine (sum_le_sum (g:=fun i=>∑ j:J, s*s*t) (fun i _=>?_)).trans_eq (by simp only [sum_const,nsmul_eq_mul,card_univ];ring); rw [_root_.map_sum]; refine Finset.sum_le_sum fun j _=>?_ ; rw [T.P.map_smul, LinearMap.smul_apply,(T.P _).map_smul]; change x i*(x j*T.P (g i) (g j))≤ _; rw [←mul_assoc]; exact (le_abs_self _).trans (by rw [abs_mul,abs_mul]; exact mul_le_mul (mul_le_mul (he i) (he j) (abs_nonneg _) hs) (scent A S h ht i j) (abs_nonneg _) (mul_nonneg hs hs))
variable [MeasurableSpace X][BorelSpace X](μ:Measure X)[μ.IsAddHaarMeasure]
lemma stickV (p:Module.Dual ℝ X)(hx:∀ i:J, ‖A.wick p ((LinearMap.proj i) ∘ₗ S)‖ ≤ s)(hs:0 ≤ s)(hp:0 ≤ t)(k:ℕ)(hk:1 ≤ k):
      let a:= (((Fintype.card J:ℝ)*Real.sqrt t)*s)*ampleP k; Fault (Amalg A μ) k ((p ∘ Prod.fst)-(p ∘ Swear.ren S L)) (a+a):=by
          intro a; apply Swear.R_F A μ S L p _ hk; have hv:0≤ (Fintype.card J:ℝ)*Real.sqrt t*s:=by positivity
          refine Lal A μ (p.comp ((L).comp S)) hv ((vein A S h ht p hx hs hp).trans_eq ?_) hk; rw [mul_pow,mul_pow,Real.sq_sqrt hp]
end
end YM.OPE.Borealis.Galea
