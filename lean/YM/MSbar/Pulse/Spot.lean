import YM.MSbar.Pulse.Torque
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Portal
open Function Filter MeasureTheory Cacao PowerSeries Finset
open scoped Topology Classical BigOperators
local notation "G"=>PowerSeries ℝ
local notation "µ"=>PowerSeries.coeff
variable {a b c t ε v e d₀ r A w B s U D δ L : ℝ} {p m : ℕ}
open Matrix MvPolynomial Further.GaussianScalar
variable {σ ι:Type} [Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ] (x:View σ)(V: Matrix σ ι ℝ) {Y : Set (View ι)} {g' h' d : View ι→ℝ} {C:Matrix ι ι ℝ}
local notation "μ!"=>fieldLaw C
local notation "P"=>PowerSeries (Pot σ)
set_option quotPrecheck false
local notation "v!"=>V*C*V.transpose
variable (F T:PowerSeries (Pot σ))
def picture (V: View σ) (f:P): PowerSeries ℝ:=PowerSeries.map (MvPolynomial.eval V) f
local notation "∆"=> (fun z:View ι=> x+V *ᵥ z)
def micro (f:P) (z:View ι):= picture (x+V *ᵥ z) f
local notation "fρ"=> micro x V
local notation "pK"=> (v!)
local notation "Zd"=> (q:ℝ)-- placeholder
variable (e:View σ)
local notation "ξ"=>Rewind F e
local notation "O"=>picture x (growP F T (v!) (p+1))
local notation "I"=>picture x (Spring (confect (v!) (Rewind F e)))
variable (h:C.PosDef)(hf:Kind F)
include h hf
lemma joint (L':PowerSeries (Pot σ))(hp:Kind L')(p:ℕ)(x':ℝ): (∫ i,taste p (Spring ((micro x V L') i)) x'∂fieldLaw C)=taste p (picture x (Spring (confect (V*C*V.transpose) L'))) x':=by
   let g(i:View ι):=x+V *ᵥ i; have he(j i):µ j (Spring ((fρ L') i))= MvPolynomial.eval (g i) (µ j (Spring L')):=by unfold micro picture; rw [show MvPolynomial.eval _ = (MvPolynomial.aeval (R:=ℝ) (g i)).toRingHom from rfl,sunshine,PowerSeries.coeff_map]
   unfold taste; simp_rw [he]; have hg(j): Integrable (fun i=> MvPolynomial.eval (g i) (µ j (Spring L'))) (fieldLaw C):=(grille V h _ x 1 (by norm_num)).integrable le_rfl
   rw [integral_finset_sum]; apply Finset.sum_congr rfl; intro i hi; rw [integral_const_mul,← goodie V x h hp]; unfold picture; rw [PowerSeries.coeff_map] -- g transparency
   exact fun j _=> (hg j).const_mul _
lemma today (p:ℕ)(t:ℝ):
       (∫ i,taste p ((micro x V T) i*Spring ((micro x V (Rewind F e)) i)) t∂fieldLaw C)=taste p (picture x (growP F T pK (p+1))*picture x (Spring (confect (v!) (Rewind F e)))) t:=by
   rw [slow (v!) F T hf (p+1) (Nat.zero_lt_succ ..) e]
   let g(i:View ι):=x+V *ᵥ i
   have hp(i) : (fρ T) i*Spring ((fρ ξ) i) = PowerSeries.map (MvPolynomial.aeval (R:=ℝ) (g i)).toRingHom (T*Spring ξ):=by unfold micro picture; rw [show MvPolynomial.eval _ = (MvPolynomial.aeval (R:=ℝ) (g i)).toRingHom from rfl,sunshine,map_mul]; try rfl
   unfold taste; simp_rw [hp,PowerSeries.coeff_map]; rw [integral_finset_sum]; apply Finset.sum_congr rfl; intro i hi; unfold picture; rw [← map_mul,PowerSeries.coeff_map]; rw [integral_const_mul]; exact congr_arg _ (aromaEval V x h _ T (hush hf) (show p+1>i from mem_range.mp hi)).symm
   exact fun j _=> show Integrable (fun z=> t^j*(MvPolynomial.eval (g z)) (µ j (T*Spring ξ))) μ! from (((grille V h _ x 1 (by norm_num)).integrable le_rfl).const_mul _)

-- experts.Burn
lemma cubed (P':ℕ) (hY:Portal.Survey (fieldLaw C) Y (micro x V (Rewind F e)) (micro x V T) g' h' d P' t r a B c D b L s) (X:Y.Nonempty)
   (hK:Belt P' I ≤ A) (hR:Belt P' (picture x (growP F T (v!) (P'+1))) ≤ w) (he: |∫ i,d i∂μ!| ≤ ε)
   (hp: |(∫ i,d i*µ 0 ((micro x V T) i)∂ μ!)-(∫ i,d i∂ μ!)* MvPolynomial.eval x (µ 0 (growP F T (v!) (P'+1)))| ≤ v)
   (hh: t*A+ε+(deltaC D B L 0 0 b t P'+a) ≤ 1/2) :
    let M:=picture x (growP F T (v!) (P'+1))
    1/2 ≤ (∫ i,purse Y h' i∂μ!) ∧
    |(∫ i,(purse Y h') i *g' i∂ μ!)/(∫ i,purse Y h' i∂μ!)-(taste P' M t+ ((∫ i,d i * µ 0 (micro x V T i)∂ μ!)-(∫ i,d i∂ μ!)* µ 0 M))| ≤ 2* Survey.fee P' t w A ε (deltaC D B L 0 0 b t P'+a) (debit P' L b B D t s (deltaC D B L 0 0 b t P') c +r) w v (t*A+ε+(deltaC D B L 0 0 b t P'+a)):= by
   intro M; apply Survey.magnitude hY (I) M X ?_ ?_ ?_ he ?_ hK hR hh
   · unfold picture;rw [PowerSeries.coeff_map,covers,_root_.map_one]; exact sugar _ (hush hf)
   · exact joint x V F h hf _ (hush hf) _ _ -- argument
   · exact today x V F T e h hf _ _
   unfold M picture; rw [PowerSeries.coeff_map]; exact hp
end YM.MSbar.Bakery.Portal
