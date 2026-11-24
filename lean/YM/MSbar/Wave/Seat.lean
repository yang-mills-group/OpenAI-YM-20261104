import YM.MSbar.Wave.Rider
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open scoped Topology Classical BigOperators ContDiff
variable {σ: Type} [Fintype σ]
open Finset MvPolynomial
local notation "µ"=> PowerSeries.coeff
local notation "V"=> View σ
local notation "Q"=> Pot σ
local notation "B"=> PowerSeries ℝ
variable (Ω B':PowerSeries ℝ)(T:PowerSeries (Pot σ))(c : Pot σ)(z: Pot σ →ₗ[ℝ]ℝ)
-- replaces scalar B'=δ_n. Prove tolerance relation. exact projection.Bt.Point.Scalar.
def Hush (X Y : PowerSeries ℝ) (n:ℕ) :Prop:=∀ i:ℕ,i<n → µ i X=µ i Y
variable {Ω B'} {p n :ℕ}
namespace Hush
lemma nit (q:ℕ) (a:ℝ) (A:PowerSeries ℝ): Hush A (A+PowerSeries.monomial q a) q:= by intro i hi; rw [_root_.map_add,PowerSeries.coeff_monomial,if_neg (by omega),add_zero]
lemma mul {P P' C C':B}(h:Hush P P' n)(p:Hush C C' n) : Hush (P*C) (P'*C') n:=by
    intro i hi; rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]; refine sum_congr rfl ?_; rintro ⟨k,u⟩ hv; have he:= mem_antidiagonal.mp hv; dsimp only at *; rw [h k (by omega),p u (by omega)]
lemma powH {P Q':B} (h:Hush P Q' n)(m:ℕ) : Hush (P^m) (Q'^m) n:=by
    induction m with
    | zero => intro i hi; simp
    | succ i ih=> rw [pow_succ,pow_succ]; exact ih.mul h
lemma invH {P Q':B} (h:Hush P Q' n) : Hush (P⁻¹) (Q'⁻¹) n:=by
    intro i hi; induction i using Nat.strong_induction_on with
    | h i ih =>
        rw [PowerSeries.coeff_inv,PowerSeries.coeff_inv,← PowerSeries.coeff_zero_eq_constantCoeff_apply,← PowerSeries.coeff_zero_eq_constantCoeff_apply,h 0 (by omega)]; split; rfl
        apply congr_arg; refine sum_congr rfl ?_; rintro ⟨u,w⟩ hu; have he:= mem_antidiagonal.mp hu; split; next hw=> -- split lhs both ifs? 
              dsimp only at *; rw [ih w hw (by omega),h u (by omega)]
        rfl
variable {T z c}
lemma fares (g:Hush Ω B' p)(hp:n<p)(j:ℕ):fare Ω T j n =fare B' T j n := Finset.sum_congr rfl (fun i _=> by rw [(Hush.mul (g.powH i) (g.invH.powH j)) n hp])
lemma seats (g:Hush Ω B' p)(hp:n<p) :µ n (bley Ω T c)=µ n (bley B' T c):=by
    unfold bley; rw [_root_.map_sub, _root_.map_sub,PowerSeries.coeff_mk,PowerSeries.coeff_mk,_root_.map_sub, _root_.map_sub,(g.powH 2) n hp,ticket,ticket,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; exact congr_arg (·- _) (sum_congr rfl (fun i _=> fares g (by omega) _))
-- ∂b_n. No coefficient formula obfusc. keep throughout p.
lemma wagon (t:Kind T)(g:Hush Ω B' p) (ha:µ 0 Ω=1)(hp :0<p):
    µ p (bley B' T c) = µ p (bley Ω T c) - (2*(µ p B' -µ p Ω)) • c:=by
    let a:=µ p B'; let b:=µ p Ω; have ht: µ p (ticket B' T)= µ p (ticket Ω T):=by
       unfold ticket; rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk]; refine sum_congr rfl (fun i hi=>?_); by_cases hh:i=0; rw [hh]; simp only [fare, (show µ 0 T=0 from t), _root_.map_zero, smul_zero, sum_const_zero]; exact (g.fares (by omega) i).symm
    have hA: µ p (B'^2-1)=µ p (Ω^2-1)+2*(a-b):=by
        simp only [map_sub, pow_two, PowerSeries.coeff_mul]; let K(x:B) : ℕ × ℕ→ℝ := fun i=> µ i.1 x * µ i.2 x; let D(i:ℕ × ℕ):= K B' i-K Ω i; have hz : ∑ i∈antidiagonal p,D i=2*(a-b):=by
            let I:=antidiagonal p; let U:Finset (ℕ × ℕ):={(0,p),(p,0)}; have hh:U ⊆ I:=by intro i hi; simp only [U, mem_insert,mem_singleton] at hi; rcases hi with h|h<;> simp [h,I]
            rw [←sum_subset hh]; swap
            · rintro ⟨u,v⟩ he hv; have hS:=mem_antidiagonal.mp he; simp only [U,mem_insert,Prod.mk.injEq,mem_singleton] at hv; unfold D K; dsimp only; rw [g u (by omega),g v (by omega),sub_self]
            have hv: µ 0 B'=1 :=(g 0 hp).symm.trans ha; unfold U; rw [sum_insert,sum_singleton]; unfold D K a b; dsimp only; rw [ha,hv]; ring; simp [Nat.ne_of_gt hp,hp.ne']
        unfold D at hz; rw [sum_sub_distrib] at hz; have hh: ∑ i∈antidiagonal p,K B' i= (∑ i∈antidiagonal p,K Ω i)+2*(a-b):=by linarith only [hz]
        change (∑ i∈antidiagonal p, K B' i) - (µ p (1:B)) = (∑ i∈antidiagonal p,K Ω i) - _ + _; rw [hh]; ring
    unfold bley; rw [_root_.map_sub,_root_.map_sub,PowerSeries.coeff_mk,PowerSeries.coeff_mk, ht,hA,add_smul, ←sub_sub]
end Hush
variable {T c z}
def Pays (b:B) (T:PowerSeries (Pot σ))(c:Q)(z: Q →ₗ[ℝ]ℝ)(n:ℕ):= µ 0 b=1∧∀ i,i≤ n→z (µ i (bley b T c))=0
variable (h:Kind T)(hc:z c≠0)
include h
lemma enough : Pays 1 T c z 0:=by
    constructor; simp; intro i hi; have hf:i=0:=by omega
    subst i; unfold bley; simp [fare,ticket,show PowerSeries.constantCoeff T=0 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,h]]
include hc
lemma earned_s (n:ℕ){b:PowerSeries ℝ}(hp:Pays b T c z n) :∃ B':PowerSeries ℝ,Hush b B' (n+1) ∧ Pays B' T c z (n+1):=by
    let i:=n+1; let p:= µ i (bley b T c); let a:= z p/(2*z c); let Y:= b+PowerSeries.monomial i a
    have hz : Hush b Y i:= Hush.nit i a b; have hv:µ i Y-µ i b=a:=by unfold Y; rw [_root_.map_add,PowerSeries.coeff_monomial]; simp
    refine ⟨Y,hz,(hz 0 (by omega)).symm.trans hp.1,fun j hj=>?_⟩; by_cases he:j=i
    · rw [he, hz.wagon h hp.1 (by omega),hv,_root_.map_sub,_root_.map_smul]; change z p-(2*a)*z c=0; unfold a; field_simp; ring
    rw [← hz.seats (by omega)]; exact hp.2 j (by omega)
lemma payer (n:ℕ): ∃ b:PowerSeries ℝ,Pays b T c z n:=by
    induction n with
    | zero=> exact ⟨1,enough h⟩
    | succ i ih=> obtain ⟨B',hp⟩:=ih; obtain ⟨B'',_,h⟩:= earned_s h hc i hp; exact ⟨B'',h⟩
end YM.MSbar.Wave
