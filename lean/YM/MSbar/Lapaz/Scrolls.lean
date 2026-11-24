import YM.MSbar.Lapaz.Dorie
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι]
variable (P:Matrix ι σ ℝ){C:Matrix σ σ ℝ} (hc:C.PosDef) {L x y a b u c r D:ℝ}
local notation "V"=> View σ
local notation "M"=> fieldLaw C
variable (h:∀ i:σ, C i i≤c) {n p:ℕ}
local notation "μ"=> fieldLaw C
variable (Q S:SpringK ι)(X:View ι){p:ℕ}(hQ:Kind Q)
local notation "Q₀"=> Rewind Q X
local notation "Ψ"=> micro X P
local notation "Ω"=> Spring
local notation "T!"=>P*C*P.transpose
local notation "E!"=>picture X
noncomputable def vow (C:Matrix σ σ ℝ)(Q:SpringK ι)(X:View ι):= picture X (Spring (confect (P*C*P.transpose) (Rewind Q X)))
noncomputable def owes(C:Matrix σ σ ℝ)(Q S :SpringK ι)(X:View ι)(p:ℕ) := picture X (growP Q S (P*C*P.transpose) (p+1))
local notation "I!"=> vow P C Q X
local notation "o!"=> owes P C Q S X p
local notation "k"=>PowerSeries.coeff
-- data.Herm.Axis meet.Local.Value. emit.Bar. coefficients ∫.
lemma sin (x: View σ):Spring (micro X P Q x)=micro X P (Spring Q) x:=by unfold micro picture; rw [show (MvPolynomial.eval _)= (MvPolynomial.aeval (R:=ℝ) (X+P*ᵥx)).toRingHom from rfl]; rw [sunshine] -- order
lemma pic (F:SpringK ι)(p:ℕ):Measurable (fun x:View σ=> PowerSeries.coeff p (micro X P F x)):=by
    unfold micro picture; simp_rw [PowerSeries.coeff_map]; exact (((vent (k p F)).continuous).comp (continuous_const.add ((Matrix.toLin' P).continuous_of_finiteDimensional))).measurable
include hc
lemma curd (p:ℕ):Integrable (fun i=> k p ((micro X P Q) i)) (fieldLaw C):=by unfold micro picture; simp_rw [PowerSeries.coeff_map]; exact (grille P hc _ X 1 (by norm_num)).integrable le_rfl
lemma pervades (i:View σ) : micro X P S i*Spring (micro X P Q₀ i)= micro X P (S*Spring Q₀) i:=by rw [sin]; exact (map_mul (PowerSeries.map (MvPolynomial.eval (X+P*ᵥi))) _ _).symm
include hQ
lemma edible (v:ℕ): (∫ i:View σ, k v (Spring ((Ψ Q₀) i)) ∂μ)= k v (vow P C Q X):=by
    simp_rw [sin]; unfold vow picture micro; simp_rw [picture, PowerSeries.coeff_map]; exact (goodie P X hc (hush hQ) v).symm -- args
lemma firm (v:ℕ)(he:v≤p): (∫ i:View σ, k v ((Ψ S) i * Spring ((Ψ Q₀) i))∂μ)= k v ((owes P C Q S X p)*vow P C Q X):=by
    simp_rw [pervades P hc]; unfold owes vow micro picture; rw [← map_mul]; simp_rw [PowerSeries.coeff_map]; rw [slow _ _ _ hQ _ (Nat.zero_lt_succ p) X]; exact (aromaEval P X hc _ S (hush hQ) (by omega:v<p+1)).symm -- h.'? select .Loop
omit hQ hc
-- belt division via recursive coeff. Tuned proj.Cl.Top.Nonuniform.P cash.
noncomputable def division (t u:ℝ)(p:ℕ):= (((p+1:ℕ):ℝ)+1)*t*(1+p*u)^p
lemma divisionP (f g:PowerSeries ℝ)(he:k 0 f=1)(hp:Belt p (g*f)≤ x) (hf:Belt p f≤y): Belt p g≤ ((p+1:ℕ)*x)*(1+↑p*y)^p:=by
    let v:=g*f; let B:=1+(p:ℝ)*y; have hy:0≤y:=le_trans (Belt_pos ..) hf; have hB:1≤B:=le_add_of_nonneg_right (by positivity); have hx:0≤x:=(Belt_pos ..).trans hp
    have hm(j:ℕ)(ht:j≤p):|PowerSeries.coeff j g|≤ x*B^j:=by
       induction j using Nat.strong_induction_on with
       | h j ih=>
          cases j with
          | zero=> rw [pow_zero,mul_one]; apply le_trans _ hp; apply le_trans _ (Belt_entry v p 0 ht); unfold v; congr 1; rw [elevator,sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,he,mul_one] -- congr. ≤ use eq
          | succ j=>
             let h(i:ℕ):= k i g*k (j+1-i) f; let m:= k (j+1) v; have he : (∑ i∈range (j+1), h i)+k (j+1) g=m:=by unfold h m v; rw [elevator, Finset.sum_range_succ _ (j+1), Nat.sub_self,he,mul_one]
             rw [eq_sub_of_add_eq' he]; apply (abs_sub ..).trans; apply le_trans (add_le_add ((Belt_entry v p _ ht).trans hp) (abs_sum_le_sum_abs ..)); refine (add_le_add_right (Finset.sum_le_sum (g:=fun _=>x*B^j*y) (fun i hi=> ?_)) _).trans ?_
             · unfold h; rw [abs_mul]; have hV:i < j+1:=Finset.mem_range.mp hi; exact mul_le_mul ((ih _ hV (by omega)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega:i ≤ j)) hx)) ((Belt_entry _ _ _ (by omega)).trans hf) (abs_nonneg _) (by positivity : 0 ≤ x*B^j)
             rw [sum_const,card_range,nsmul_eq_mul]; apply (add_le_add (le_mul_of_one_le_right hx (show 1 ≤ B^j from one_le_pow₀ hB)) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (by positivity))).trans_eq; rw [pow_succ]; unfold B;ring
    apply (sum_le_sum (s:=range (p+1)) (g:=fun _=> x*B^p) (fun i hi=>?_)).trans ?_
    · rw [sum_const,nsmul_eq_mul,card_range]; exact le_of_eq (mul_assoc ..).symm
    have he:i≤p:=Nat.lt_succ_iff.mp (mem_range.mp hi); exact (hm _ he).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB he) hx)
end YM.MSbar.Lapaz
