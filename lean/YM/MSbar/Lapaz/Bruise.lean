import YM.MSbar.Lapaz.Scrolls
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
variable (Q S:SpringK ι)(X:View ι){p:ℕ}(hQ:Kind Q)
local notation "Q₀"=> Rewind Q X
local notation "Ψ"=> micro X P
local notation "Ω"=> Spring
local notation "T!"=>P*C*P.transpose
local notation "E!"=>picture X
local notation "I!"=> vow P C Q X
local notation "o!"=> owes P C Q S X p
local notation "k"=>PowerSeries.coeff
variable {A B t R W d r1 r2:ℝ}{Z: Set (View σ)}{s:ℕ}
variable (hS:∀ x:View σ, Belt p (micro X P (Rewind Q X) x)≤A*(1+‖x‖)^s ∧ Belt p (micro X P S x) ≤ B*(1+‖x‖)^s)
include hS hQ
local notation "F"=> micro X P (Rewind Q X)
local notation "f"=> micro X P S
lemma winds (x:View σ): Belt p (Spring (F x)) ≤ bag p A * (1+‖x‖)^(s*p) ∧ Belt p ((f x)*Spring (F x)) ≤ B* bag p A* (1+‖x‖)^(s+s*p):=by
    have hA:0≤ A:=by have hp:= (Belt_pos p _).trans ((hS 0).1); simpa using hp
    have hB:0≤ B:=by have hp:= (Belt_pos p _).trans ((hS 0).2); simpa using hp
    let x':=1+‖x‖; have hp(x): Kind (F x):=by unfold Kind Rewind micro picture; rw [PowerSeries.coeff_map]; change eval _ (k 0 Q₀)=(0:ℝ); rw [hush hQ, _root_.map_zero]
    have hX:1 ≤ x':=le_add_of_nonneg_right (norm_nonneg _); let t(p':ℕ):=x'^p'; have ht(i:ℕ):0≤t i:=pow_nonneg (zero_le_one.trans hX) _
    have ht' : Belt p (Spring (F x)) ≤ bag p A*t (s*p):= by
         refine (lavish _ (hp _) p (hS _|>.1)).trans ?_; unfold bag; rw [sum_mul]; refine sum_le_sum fun i hi=>?_; change _*(A*t s)^i≤_; unfold t; rw [mul_pow]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA _)) (by positivity)) (le_of_eq (mul_assoc ..).symm); rw [← pow_mul]; apply pow_le_pow_right₀ hX; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (mem_range.mp hi))
    exact ⟨ht',(Belt_product ..).trans ((mul_le_mul (hS _|>.2) ht' (Belt_pos ..) (mul_nonneg hB (ht s))).trans_eq (by unfold t x'; ring))⟩
include hc h
lemma earth (u:ℕ) : Integrable (fun i=> PowerSeries.coeff u (Spring (micro X P Q₀ i))) (fieldLaw C) ∧ Integrable (fun i=> k u (f i*Spring (F i))) (fieldLaw C):=by simp_rw [pervades P hc, Lapaz.sin]; exact ⟨curd P hc _ _ _,curd P hc _ _ _⟩
variable (D': View σ→ℝ)(hr:Measurable D')(hd:∀ i,|D' i| ≤ d)
include hr hd
lemma embers : Integrable D' (fieldLaw C) ∧ Integrable (fun i:View σ=> D' i*k 0 ((micro X P S) i)) (fieldLaw C) ∧ |∫ i,D' i∂M|≤ d ∧ |∫ i,D' i * k 0 ((micro X P S) i)∂ M| ≤ d*B*boreo (Fintype.card σ) c s :=by
    have he:0 ≤ d := (abs_nonneg _).trans (hd 0); have ht(i):|k 0 ((micro X P S) i)| ≤ B*(1+‖i‖)^s:= (Belt_entry _ _ 0 (Nat.zero_le p)).trans ((hS i).2); have hB:0 ≤ B:=by have hx:= le_trans (abs_nonneg _) (ht (0:View σ)); simpa using hx
    have hx : Integrable D' M:= (integrable_const (μ:=fieldLaw C) d).mono' hr.aestronglyMeasurable (ae_of_all _ hd)
    obtain ⟨h,hg⟩:= spread hc h _ (hr.mul (pic P X S 0)) (fun x=> (abs_mul ..).trans_le ((mul_le_mul (hd x) (ht x) (abs_nonneg _) he).trans_eq (mul_assoc ..).symm)) (mul_nonneg he hB); exact ⟨hx,h,(norm_integral_le_integral_norm _).trans ((integral_mono hx.norm (integrable_const d) hd).trans_eq (by simp)), hg⟩
variable (hz:MeasurableSet Z)(hμ:(fieldLaw C).real Z ≤ R)(hy:0<L)(ht :0≤ t)(hp :t≤ 1)
include hz hμ hy ht hp
local notation "z1"=> fish (Fintype.card σ) (s*p) c (bag p A) L R
local notation "z2"=> fish (Fintype.card σ) (s+s*p) c (B*bag p A) L R
local notation "r1'"=>fish (Fintype.card σ) 0 c d L R
local notation "r2'"=>fish (Fintype.card σ) s c (d*B) L R
lemma trace : |∫ i in Z, taste p (Spring (F i)) t + D' i∂M|≤ z1+r1' ∧ |∫ i in Z,taste p (f i*Spring (F i)) t + D' i*k 0 (f i)∂M| ≤ z2+r2':=by
    have hA:0≤ A:=by have hp:= (Belt_pos p _).trans ((hS 0).1); simpa using hp
    have hB:0≤B:=by have hp:= (Belt_pos p _).trans ((hS 0).2); simpa using hp
    have hs:0≤ bag p A:=sum_nonneg fun i _=> mul_nonneg (by positivity) (pow_nonneg hA _)
    let T'(g:SpringK ι)(i):=taste p (Ψ g i) t; have hx(g:SpringK ι): Integrable (T' g) M∧Measurable (T' g):=by
         unfold T' taste; exact ⟨integrable_finset_sum _ (fun i _=> ((curd P hc g X i).const_mul _)), Finset.measurable_sum _ fun i _=> (pic P X g i).const_mul _⟩
    obtain ⟨hv,hH,-⟩:= embers P hc h Q S X hQ hS D' hr hd
    let V₀:= Spring Q₀; let v:=S*V₀
    have ht(i): |T' V₀ i|≤bag p A*(1+‖i‖)^(s*p) :=by unfold T' V₀; rw [← Lapaz.sin]; exact (taste_pays ht hp _).trans (winds P Q S X hQ hS _|>.1)
    have hD:= (abs_nonneg _).trans (hd 0); have hD':0 ≤d:=hD
    have hT(i:View σ): Measurable D':=hr
    constructor
    · simp_rw [Lapaz.sin]; change |∫ i in Z,T' V₀ i+D' i∂M|≤ _; rw [integral_add ((hx V₀|>.1).integrableOn) hv.integrableOn] -- simp may rw IQ.total wrong
      exact (abs_add_le ..).trans (add_le_add (surf hc h _ _ hz hμ hy (hx V₀|>.2) ht hs) (surf hc h _ _ hz hμ hy hr (fun x=>by simpa using hd x) hD))
    simp_rw [pervades P hc]; change |∫ i in Z,T' v i+D' i*k 0 (f i)∂M|≤ _; rw [integral_add ((hx v|>.1).integrableOn)];
    · apply (abs_add_le ..).trans; refine add_le_add (surf hc h _ _ hz hμ hy (hx v|>.2) (fun i=>?_) (mul_nonneg hB hs)) (surf hc h _ _ hz hμ hy (hr.mul (pic P X S 0)) (fun i=> ((abs_mul ..).trans_le ((mul_le_mul (hd i) ((Belt_entry (f i) _ 0 (Nat.zero_le p)).trans (hS i|>.2)) (abs_nonneg _) hD).trans_eq (mul_assoc ..).symm))) (mul_nonneg hD hB))
      unfold T'; unfold v V₀; rw [← pervades P hc Q]; exact (taste_pays ‹0 ≤ t› hp _).trans (winds P Q S X hQ hS _|>.2) -- he shape ht shadow
    exact hH.integrableOn
end YM.MSbar.Lapaz
