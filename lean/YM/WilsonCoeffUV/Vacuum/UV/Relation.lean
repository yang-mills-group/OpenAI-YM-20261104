import YM.WilsonCoeffUV.Vacuum.UV.AllOrders
/-!
# Uniform charge of cross-level powers
Conjugation of cost series. `B` multiplicative law is under actual
variable scale map, not just polynomial multiplication. Travel along an arbitrary
window and back, charges anchored once, path notation. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W T :Credit}{ξ:Type*}

-- centered pull of A under variable rescaled by B

def reel (B :Cost): Cost →+* Cost := (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (by simp: constantCoeff (B*X)=0))).toRingHom
lemma reel_C (B:Cost) (a:ℝ): reel B (C a)=C a:= by change substAlgHom _ _= _; rw [coe_substAlgHom]; exact subst_C a
lemma reel_X (B:Cost):reel B X=B*X := substAlgHom_X _
def chartB (A B:Cost): Cost:= reel B A * B
lemma hit_chart (A B:Cost): chartB A B*X=reel B (A*X):=by rw [chartB,mul_assoc,map_mul,reel_X]
lemma reel_chart (A B:Cost): (reel B).comp (reel A)=reel (chartB A B):=by
   symm; refine serial_ext (by rw [reel_X];simp) (fun i=>?_) ?_
   · rw [RingHom.comp_apply,reel_C,reel_C,reel_C]
   rw [RingHom.comp_apply,reel_X,reel_X,hit_chart]
lemma reel_apply (A B:Cost): reel B A= subst (B*X) A:= by change substAlgHom _ _= _; rw [coe_substAlgHom]
@[simp] lemma reel_one (A:Cost): reel 1 A=A:=by rw [reel_apply,one_mul]; simp
lemma chart_assoc (A B D:Cost): chartB (chartB A B) D=chartB A (chartB B D):= by
   unfold chartB; rw [map_mul,mul_assoc]; exact congrArg (· * (reel D B * D)) (DFunLike.congr_fun (reel_chart B D) A)
@[simp] lemma chart_one (A:Cost): chartB A 1=A:=by rw [chartB,reel_one,mul_one]
@[simp] lemma chart_ones (A:Cost):chartB 1 A=A:=by rw [chartB,map_one,one_mul]
lemma chart_forward {f:Cost}(p:constantCoeff f=1):chartB (back f) (pace f)=1:=by
    apply mul_right_cancel₀ (b:=PowerSeries.X) X_ne_zero; rw [one_mul,hit_chart,fresh_back,reel_apply]; exact reverse_left p
lemma chart_backward {f:Cost}(p:constantCoeff f=1):chartB (pace f) (back f)=1:=by
    apply mul_right_cancel₀ (b:=PowerSeries.X) X_ne_zero; rw [one_mul,hit_chart,reel_apply,fresh_back]; exact reverse_right p
lemma chart_coeff (A B:Cost)(i:ℕ): coeff i (chartB A B) = ∑ j∈ Finset.range (i+1), coeff j A * coeff (i-j) (B^(j+1)):=by
    unfold chartB; rw [(Equal.mul (filtered (show constantCoeff (reel B X)=0 by rw [reel_X]; simp) (shave A (i+1))) (Equal.refl B _)) i i.lt_succ_self, map_sum,Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [map_mul (reel B),map_pow (reel B),reel_X,reel_C,mul_pow]; rw [show C (coeff j A)*(B^j*X^j)*B=(C (coeff j A)*B^(j+1))*X^j by ring, coeff_mul_X_pow', if_pos (by have he:= Finset.mem_range.mp hj; omega),coeff_C_mul]
lemma cc_chart {A B:Cost}(p:constantCoeff A=1)(h:constantCoeff B=1): constantCoeff (chartB A B)=1:=by rw [←coeff_zero_eq_constantCoeff_apply,chart_coeff]; simp [p,h]
lemma inflow {A B:Cost}(p:constantCoeff A=1)(i:ℕ): coeff i (chartB A B)=coeff i B+∑ j∈(Finset.range (i+1)).erase 0, coeff j A * coeff (i-j) (B^(j+1)):= by
    rw [chart_coeff,← Finset.add_sum_erase _ _ (show 0∈ Finset.range (i+1) from Finset.mem_range.mpr (by omega)), coeff_zero_eq_constantCoeff_apply, p,one_mul,pow_one]; simp

section span
variable {x θ:ξ→ℝ}{p q f g:Colorback ξ}
lemma clipped_dual (h:Brite x θ)(hf:∀ j,constantCoeff (f j)=1)(hg:∀ j,constantCoeff (g j)=1)(hx:∀ j ≤ i, Weft x θ f g j)(ha:∀ j,chartB (f j) (p j)=1)(hb:∀ j,chartB (g j) (q j)=1): Weft x θ p q i:=by
  induction i using Nat.strong_induction_on with
  | h i ih=>
    let S:= (Finset.range (i+1)).erase 0
    have hh (j:ℕ)(e:j∈S): clips x θ (fun v=>coeff j (f v)*coeff (i-j) ((p v)^(j+1))) (fun v=> coeff j (g v)*coeff (i-j) ((q v)^(j+1))):=by
       obtain ⟨hz,h⟩:= Finset.mem_erase.mp e; have hv:= Finset.mem_range.mp h
       refine (hx j (by omega)).mul ?_
       exact (show Weft x θ (p^(j+1)) (q^(j+1)) (i-j) from clipped_pow (by assumption) _ fun k he=> ih _ (by omega) fun y hy=> hx y (by omega))
    have he (P F:Cost)(p: chartB F P=1)(h:constantCoeff F=1) : coeff i P= coeff i (1:Cost)-∑ j∈S,coeff j F * coeff (i-j) (P^(j+1)):= by have he:= inflow (B:=P) h i; rw [p] at he; rw [he,add_sub_cancel_right]
    unfold Weft; simp_rw [fun v=> he _ _ (ha v) (hf v),fun v=> he _ _ (hb v) (hg v)]; exact (clips.one h _).sub (clips.sum h hh) h
-- variable comp window: static I terms clipped, finite count bounded by price x
variable {n':ℕ}{n:ξ→ℕ}{A B: ξ→ℕ→Cost}
noncomputable def palmB (A:ℕ→ Cost): ℕ → Cost | 0=> 1 | i+1=>chartB (A i) (palmB A i)
-- backward compound

noncomputable def leeB (A:ℕ→Cost): ℕ→Cost|0=>1 | i+1=>chartB (leeB A i) (A i)
lemma palm_joins (A:ℕ→ Cost)(m k:ℕ): palmB A (m+k)=chartB (palmB (fun i=>A (m+i)) k) (palmB A m):= by
    induction k with
    | zero=>rw [Nat.add_zero,palmB,chart_ones]
    | succ i ih=>rw [show m+(i+1)=m+i+1 by omega,palmB,ih,palmB,chart_assoc]
lemma lee_joins (A:ℕ→Cost)(m k:ℕ): leeB A (m+k)=chartB (leeB A m) (leeB (fun i=>A (m+i)) k):=by
    induction k with
    | zero=>rw [Nat.add_zero,leeB,chart_one]
    | succ i ih=> rw [show m+(i+1)=m+i+1 by omega,leeB,ih,leeB,chart_assoc]
lemma deckDual (A B:ℕ→Cost)(h:∀ i<n',chartB (A i) (B i)=1)(p:∀ i<n',chartB (B i) (A i)=1): chartB (palmB A n') (leeB B n')=1 ∧ chartB (leeB B n') (palmB A n')=1:=by
   induction n' with
   | zero=> simp [palmB,leeB]
   | succ i ih=>
     obtain ⟨e,b⟩:= ih (fun j hj=>h j (by omega)) fun j hj=>p j (by omega)
     rw [palmB,leeB]; constructor
     · rw [chart_assoc,←chart_assoc _ (leeB B i) _,e,chart_ones,h _ (by omega)]
     rw [chart_assoc,←chart_assoc _ (A i) _, p _ (by omega),chart_ones,b]
lemma cc_palm {A:ℕ→ Cost}(p:∀ j<n',constantCoeff (A j)=1): constantCoeff (palmB A n')=1:= by
   induction n' with
   | zero=> exact map_one _
   | succ i ih=> exact cc_chart (p i (by omega)) (ih fun j hj=> p j (by omega))
lemma cc_lee {A:ℕ→ Cost}(p:∀ j<n',constantCoeff (A j)=1): constantCoeff (leeB A n')=1:=by induction n' with
                                                                                           | zero=> exact map_one _
                                                                                           | succ i ih=> exact cc_chart (ih fun j hj=>p j (by omega)) (p i (by omega))
-- span bridge costs for visits indexed externally to allow induction.
structure Portago (n:ξ→ℕ) where
    cargo : ξ
    coin:ℕ
    credit : coin ≤ n cargo
structure Jag (n:ξ→ℕ) where
    cargo : ξ
    coin:ℕ
    credit : coin < n cargo

abbrev rub (n:ξ→ℕ)(P:ξ→ℝ): Jag n→ℝ:= fun i=>P i.cargo
abbrev rubP (n:ξ→ℕ)(P:ξ→ℝ) :Portago n → ℝ:=fun i=>P i.cargo
def gems (n:ξ→ℕ)(A:ξ→ℕ→ Cost) : Colorback (Portago n):= fun i=>palmB (A i.cargo) i.coin
abbrev gemsP (n:ξ→ℕ)(A:ξ→ℕ→Cost): Colorback (Jag n) := fun i=> A i.cargo i.coin
private lemma clip_jag (h: Weft (rubP n x) (rubP n θ) (gems n A) (gems n B) i): Weft (rub n x) (rub n θ) (fun i=>palmB (A i.cargo) i.coin) (fun i=>palmB (B i.cargo) i.coin) i:= by
   obtain ⟨d,c,p,e⟩:= h; exact ⟨d,c,p,fun i=> e ⟨i.cargo,i.coin, i.credit.le⟩⟩
lemma shiny (h:Brite x θ)(hv:∀ a:ξ,(n a:ℝ)≤ x a)(he:∀ a:ξ,∀ j<n a, constantCoeff (A a j)=1)(hg:∀ a:ξ,∀ j<n a,constantCoeff (B a j)=1)(hy:∀ j ≤ i,Weft (rub n x) (rub n θ) (gemsP n A) (gemsP n B) j): Weft (rubP n x) (rubP n θ) (gems n A) (gems n B) i:=by
   induction i using Nat.strong_induction_on with
   | h i ih=>
     let S:= (Finset.range (i+1)).erase 0; let D:Colorback (Jag n):=fun j=> palmB (A j.cargo) j.coin; let E:Colorback (Jag n):= fun j=>palmB (B j.cargo) j.coin
     have ht:Brite (rub n x) (rub n θ):= ⟨fun i=>h.large _,fun i=>h.dist _⟩
     have hh (j:ℕ)(e:j∈S): clips (rub n x) (rub n θ) (fun v=>coeff j (gemsP n A v)*coeff (i-j) ((D v)^(j+1))) (fun v=> coeff j (gemsP n B v)*coeff (i-j) ((E v)^(j+1))):= by
        obtain ⟨hz,h⟩:= Finset.mem_erase.mp e; have hv:= Finset.mem_range.mp h
        have he: Weft (rub n x) (rub n θ) (D^(j+1)) (E^(j+1)) (i-j):= clipped_pow ht _ (fun k he=> clip_jag (ih k (by omega) (fun l hl=> hy l (by omega))))
        refine (hy j (by omega)).mul ?_; simpa only [Weft,Pi.pow_apply] using he
     by_cases e:i=0
     · subst i; unfold Weft; simp_rw [gems,coeff_zero_eq_constantCoeff_apply, fun v:Portago n=> cc_palm (A:=A v.cargo) (n':=v.coin) (fun j hj=>he _ j (lt_of_lt_of_le hj v.credit)),fun v:Portago n=> cc_palm (A:=B v.cargo) (n':=v.coin) (fun j hj=>hg _ j (lt_of_lt_of_le hj v.credit))]; exact clips.one ⟨fun i=>h.large _,fun i=>h.dist _⟩ _
     obtain ⟨d,c,p,H⟩:= clips.sum ht hh; refine ⟨d+1,c,p,fun a=>?_⟩
     obtain ⟨t,m,w⟩:=a
     set y:= x t; let Q:= c*y^d
     have ha: ∀ j≤m,twain ((j:ℝ)*Q) (θ t) (coeff i (palmB (A t) j)) (coeff i (palmB (B t) j)):= by
        intro k; induction k with
        | zero=> intro _; simp_rw [palmB,coeff_one,if_neg e]; norm_num; exact twain.zero _
        | succ j hj=> intro x; let b:Jag n:= ⟨t,j,by omega⟩; rw [palmB,palmB,inflow (A:=A _ _) (he t j b.credit),inflow (A:=B _ _) (hg t j b.credit)]; push_cast; rw [add_mul,one_mul]; exact (hj (by omega)).add (H b)
     have hx:1≤y:=h.large t; have hl:(m:ℝ)≤y:= le_trans (by exact_mod_cast w) (hv t)
     refine (ha m le_rfl).lift (le_trans (mul_le_mul_of_nonneg_right hl (show 0≤Q by unfold Q; positivity)) ?_) (h.dist _)
     change _≤ c*y^(d+1); unfold Q; exact le_of_eq (by ring)
end span
end YM.WilsonCoeffUV.Bank
