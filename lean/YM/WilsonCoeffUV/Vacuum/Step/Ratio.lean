import YM.WilsonCoeffUV.Vacuum.Step.PairTariff
/-!
# Adjacent ratio powers, explicit Lipschitz form finite coefficient access
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {i j ℓ n:ℕ}{σ A δ:ℝ} {I J V:Type*}

-- abstract; one price for input scalar X≥1.
def clips [NormedAddCommGroup V](x θ:I→ℝ)(f g:I→ V): Prop:= ∃ d:ℕ,∃ C:ℝ,0≤C∧∀ i,twain (C*(x i)^d) (θ i) (f i) (g i)
structure Brite {I: Type*} (x θ : I→ℝ): Prop where
  large i : 1≤x i
  dist i : 0≤θ i
section
variable [NormedAddCommGroup V] {x θ:I→ℝ}{f g t u: I→ V}
lemma clips.zero : clips x θ (0:I→V) (0:I→V):= ⟨0,0,le_rfl,fun i=>by rw [zero_mul]; exact twain.zero _⟩
lemma clips.one (h:Brite x θ)(c:V): clips x θ (fun _=>c) (fun _=>c):=⟨0,‖c‖,norm_nonneg _,fun i=>by rw [pow_zero,mul_one]; exact twain.one _ _ (h.dist _) le_rfl⟩
lemma clips.start (h:∀ i,twain (x i) (θ i) (f i) (g i)): clips x θ f g:= ⟨1,1,zero_le_one,fun i=>by rw [pow_one,one_mul]; exact h i⟩
lemma roof_pair (x A B:ℝ)(h:1≤x)(p:0≤ A)(q:0≤ B)(i j:ℕ): A*x^i+B*x^j ≤(A+B)*x^(i+j):= by rw [add_mul]; gcongr <;> omega
lemma clips.add (h:clips x θ f g)(e:clips x θ t u)(p:Brite x θ): clips x θ (f+t) (g+u):=by
   obtain ⟨i,a,ha,h⟩:=h; obtain ⟨j,b,hb,G⟩:=e; exact ⟨_,_,add_nonneg ha hb, fun s=> ((h s).add (G s)).lift (roof_pair _ _ _ (p.large s) ha hb i j) (p.dist _)⟩
lemma clips.neg (h:clips x θ f g): clips x θ (-f) (-g):=by obtain ⟨d,c,h,e⟩:=h; exact ⟨d,c,h,fun i=>(e i).neg⟩
lemma clips.sub (h:clips x θ f g)(e:clips x θ t u)(p:Brite x θ): clips x θ (f-t) (g-u):= by simpa only [sub_eq_add_neg] using h.add e.neg p
lemma clips.sum (p:Brite x θ){a:Finset J}{f g:J→I→V}(h:∀ i∈a,clips x θ (f i) (g i)): clips x θ (fun i=>∑ j∈a, f j i) (fun i=>∑ j∈a,g j i):=by
   classical
   induction a using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact clips.zero
   | @insert i s he H=> simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=> h j (Finset.mem_insert_of_mem hj)) p
variable [NormedSpace ℝ V]
lemma clips.μ {u v:I→ℝ}(h: clips x θ f g)(p:clips x θ u v): clips x θ (fun i=> u i • f i) (fun i=> v i • g i):= by
   obtain ⟨i,a,ha,h⟩:=h; obtain ⟨j,b,hb,e⟩:=p
   refine ⟨i+j, 2*a*b, by positivity,fun t=> ?_⟩
   rw [pow_add,show 2*a*b*(_*_)=2*(a*x t^i)*(b*x t^j) by ring]; exact (h t).μ (e t)
lemma clips.mul {x θ f g t u:I→ℝ}(h:clips x θ f g)(p:clips x θ t u): clips x θ (fun i=> f i*t i) (fun i=>g i*u i):= p.μ h
end

abbrev Colorback (I:Type*) := I→ PowerSeries ℝ

def Weft {I:Type*}(x θ:I→ℝ)(p q: Colorback I)(i:ℕ): Prop:=clips x θ (fun v=>coeff i (p v)) (fun v=>coeff i (q v))
lemma alloy_square {P: PowerSeries ℝ}(p:constantCoeff P=1): back P*back P= P.subst (back P * X) := by
    have he:= bridge_price p; rw [← fresh_back] at he; let B:= back P
    have hb : IsUnit (constantCoeff B):=by rw [back_cc p]; simp
    have ht: B⁻¹ * B=1:= PowerSeries.inv_mul_cancel _ hb.ne_zero
    change B*B=P.subst (B*X); change P.subst (B*X)*(B⁻¹)^2=1 at he; calc
      _ = (P.subst (B*X)*(B⁻¹)^2)*(B*B):= by rw [he]; simp
      _ = P.subst (B*X)*((B⁻¹*B)*(B⁻¹*B)):=by ring
      _ = _:= by rw [ht]; simp

section laws
variable {x θ:I→ℝ}{p q f g:Colorback I}
lemma clipped_mul (h:Brite x θ)(hp:∀ j≤ i,Weft x θ p q j)(hq:∀ j≤ i,Weft x θ f g j): Weft x θ (p*f) (q*g) i:=by
    unfold Weft; simp_rw [Pi.mul_apply,coeff_mul]; apply clips.sum h; intro j hj; have he:= Finset.mem_antidiagonal.mp hj; exact (hp j.1 (by omega)).mul (hq j.2 (by omega))
lemma clipped_pow (h:Brite x θ)(b)(hp:∀ j≤ i,Weft x θ p q j): Weft x θ (p^b) (q^b) i := by
    induction b generalizing i with
    | zero=> simp only [pow_zero]; exact clips.one h _
    | succ k ih=> rw [pow_succ,pow_succ]; apply clipped_mul h _ hp; intro j hj; exact ih (fun l hl=> hp l (hl.trans hj))
lemma stem_amt (b: PowerSeries ℝ)(he:constantCoeff b=1) (i:ℕ)(p:0< i): coeff i b⁻¹= -(∑ j∈ (Finset.antidiagonal i).erase (0,i), coeff j.1 b*coeff j.2 b⁻¹):=by
    have hp : IsUnit (constantCoeff b):=by rw [he]; simp
    have ht:= congr_arg (coeff i) (PowerSeries.mul_inv_cancel b hp.ne_zero)
    rw [coeff_one,if_neg p.ne',coeff_mul,← Finset.add_sum_erase _ _ (show (0,i)∈ _ from Finset.mem_antidiagonal.mpr (by simp)),coeff_zero_eq_constantCoeff_apply,he,one_mul] at ht; exact eq_neg_of_add_eq_zero_left ht
lemma clipped_inv (h:Brite x θ)(he:∀ j,constantCoeff (p j)=1)(hh:∀ j,constantCoeff (q j)=1)(hp:∀ j≤ i,Weft x θ p q j): Weft x θ (fun i=>(p i)⁻¹) (fun i=>(q i)⁻¹) i:= by
    induction i using Nat.strong_induction_on with
    | h i ih=>
      by_cases H:i=0
      · subst i; unfold Weft; simp [he,hh]; exact clips.one h _
      unfold Weft; simp_rw [stem_amt _ (he _) i (by omega),stem_amt _ (hh _) i (by omega)]
      have hx (j) (hx:j∈ (Finset.antidiagonal i).erase (0,i)) : clips x θ (fun v=>coeff j.1 (p v)*coeff j.2 (p v)⁻¹) (fun v=> coeff j.1 (q v)*coeff j.2 (q v)⁻¹):= by
        obtain ⟨hb,hv⟩:= Finset.mem_erase.mp hx; have ha:= Finset.mem_antidiagonal.mp hv; have hm : j.2< i:= by by_contra H; exact hb (Prod.ext (show j.1=0 by omega) (show j.2=i by omega))
        exact (hp j.1 (by omega)).mul (ih _ hm (fun j hj=> hp j (hj.trans hm.le)))
      exact (clips.sum h hx).neg

lemma signal_square (b:PowerSeries ℝ)(p:constantCoeff b=1) (i:ℕ)(hi:0< i):
    let f:=back b; let Q:= (Finset.antidiagonal i).erase (0,i);
    coeff i f=(1/2:ℝ) * ((∑ j∈(Finset.range (i+1)).erase 0, coeff j b * coeff (i-j) (f^j))-∑ j∈Q.erase (i,0), coeff j.1 f*coeff j.2 f):=by
     intro f Q; have h₁ : (0,i)∈ Finset.antidiagonal i:= Finset.mem_antidiagonal.mpr (by simp); have h₂ : (i,0)∈ Q:= Finset.mem_erase.mpr ⟨by simp [hi.ne'],Finset.mem_antidiagonal.mpr (by simp)⟩
     have h : coeff i (f*f)=2*coeff i f+∑ j∈Q.erase (i,0),coeff j.1 f*coeff j.2 f:=by
       rw [coeff_mul,← Finset.add_sum_erase _ _ h₁, ← Finset.add_sum_erase _ _ h₂]; simp_rw [coeff_zero_eq_constantCoeff_apply, show constantCoeff f=1 from back_cc p, one_mul,mul_one,two_mul,add_assoc]
     have hf: IsUnit (constantCoeff f):=by rw [back_cc p]; simp
     let F: PowerSeries ℝ→+* PowerSeries ℝ:=(substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (by simp:constantCoeff (f*X)=0))).toRingHom
     have ht:F b=f*f:=by rw [show f*f=_ from alloy_square p]; change substAlgHom _ _=_; rw [coe_substAlgHom]
     have hy a:F (C a)=C a:=by change substAlgHom _ _= _; rw [coe_substAlgHom]; exact subst_C a
     have hz:F X=f*X:=substAlgHom_X _
     rw [← ht, filtered (show constantCoeff (F X)=0 by rw [hz]; simp) (shave b _) i i.lt_succ_self, map_sum, map_sum,← Finset.add_sum_erase _ _ (show 0∈ Finset.range (i+1) from Finset.mem_range.mpr (by omega)),pow_zero,mul_one,hy,coeff_C,if_neg hi.ne',zero_add] at h
     have H : (∑ j∈(Finset.range (i+1)).erase 0, coeff j b * coeff (i-j) (f^j))=2*coeff i f+∑ j∈Q.erase (i,0),coeff j.1 f*coeff j.2 f:=by
       rw [← h]; apply Finset.sum_congr rfl; intro j hj; rw [map_mul, map_pow F,hz,hy,mul_pow,←mul_assoc, coeff_mul_X_pow', if_pos ?_,coeff_C_mul]
       have he:= Finset.mem_range.mp (Finset.mem_erase.mp hj).2; omega
     rw [H,add_sub_cancel_right]; ring
lemma clipped_back (h:Brite x θ)(he:∀ j,constantCoeff (p j)=1)(hh:∀ j,constantCoeff (q j)=1)(hp:∀ j≤ i,Weft x θ p q j): Weft x θ (fun i=>back (p i)) (fun i=>back (q i)) i:= by
   induction i using Nat.strong_induction_on with
   | h i ih=>
     by_cases hl:i=0
     · subst i; unfold Weft; simp_rw [coeff_zero_eq_constantCoeff_apply, back_cc (he _), back_cc (hh _)]; exact clips.one h _
     have hy : 0< i:=by omega
     let P i:= back (p i); let Q i:= back (q i); let F: Finset ℕ:= (Finset.range (i+1)).erase 0; let G:= ((Finset.antidiagonal i).erase (0,i)).erase (i,0)
     have ha j (hj:j∈F): clips x θ (fun v=> coeff j (p v) * coeff (i-j) ((P v)^j)) (fun v=>coeff j (q v)*coeff (i-j) ((Q v)^j)):= by
        obtain ⟨ha,hb⟩:= Finset.mem_erase.mp hj
        refine (hp j (by have h:= Finset.mem_range.mp hb; omega)).mul ?_
        have ht:=clipped_pow h (p:=P) (q:=Q) (i:=i-j) j fun l he=> ih l (by omega) (fun s hs=> hp s (by omega))
        simpa only [Weft,Pi.pow_apply] using ht
     have hf (j)(hj:j∈G): clips x θ (fun v=> coeff j.1 (P v)*coeff j.2 (P v)) (fun v=> coeff j.1 (Q v)*coeff j.2 (Q v)):= by
        obtain ⟨he,hp'⟩:= Finset.mem_erase.mp hj; obtain ⟨ha,hc⟩:= Finset.mem_erase.mp hp'; have ht:= Finset.mem_antidiagonal.mp hc
        have h₁ : j.1< i:=by by_contra h; exact he (Prod.ext (show j.1=i by omega) (show j.2=0 by omega))
        have h₂ : j.2< i:=by by_contra h; exact ha (Prod.ext (show j.1=0 by omega) (show j.2=i by omega))
        exact (ih _ h₁ fun j hj=> hp j (hj.trans h₁.le)).mul (ih _ h₂ fun j hj=> hp j (hj.trans h₂.le))
     have hk:= (clips.one h (1/2:ℝ)).mul ((clips.sum h ha).sub (clips.sum h hf) h)
     unfold Weft;
     simp_rw [signal_square _ (he _) i hy,signal_square _ (hh _) i hy]; exact hk
lemma winter_μ (h:Brite x θ)(a b:ℕ)(he:∀ j,constantCoeff (p j)=1)(hh:∀ j,constantCoeff (q j)=1)(hp:∀ j≤ i,Weft x θ p q j): Weft x θ (fun i=>back (p i)^a * ((back (p i))⁻¹)^b) (fun i=>back (q i)^a*((back (q i))⁻¹)^b) i := by
   let U i:=back (p i); let V i:=back (q i)
   have H (j) (hj:j≤ i): Weft x θ U V j:= clipped_back h he hh (fun t ht=>hp t (ht.trans hj));
   let P i := (U i)⁻¹; let Q i:= (V i)⁻¹
   have ht (j)(hj:j≤ i): Weft x θ P Q j:=clipped_inv (p:=U) (q:=V) h (fun v=>back_cc (he _)) (fun v=>back_cc (hh _)) fun t ht=> H t (ht.trans hj)
   have hu:= clipped_mul (p:=U^a) (q:=V^a) (f:=P^b) (g:=Q^b) (i:=i) h (fun i hi=> clipped_pow h a (fun j hj=> H _ (hj.trans hi))) (fun i hi=> clipped_pow h b (fun j hj=> ht j (hj.trans hi)))
   simp only [Weft,Pi.mul_apply,Pi.pow_apply] at hu; exact hu
end laws

-- eliminate as one finite post-demand.
structure ScalarGate (n:ℕ) where
   x:ℝ
   θ:ℝ
   large: 1≤x
   away :0≤θ
   k:PowerSeries ℝ
   k': PowerSeries ℝ
   cc: constantCoeff k=1
   cc': constantCoeff k'=1
   bound j:j≤n→ twain x θ (coeff j k) (coeff j k')

theorem scalar_receipt (i a b:ℕ): ∃ n:ℕ,∃ C:ℝ,0≤ C ∧ ∀ (A:ScalarGate i), twain (C*A.x^n) A.θ (coeff i ((back A.k)^a*((back A.k)⁻¹)^b)) (coeff i ((back A.k')^a*((back A.k')⁻¹)^b)) :=
   winter_μ (I:=ScalarGate i) ⟨fun i=>i.large,fun i=>i.away⟩ a b (fun j=>j.cc) (fun j=>j.cc') fun j hj=> clips.start fun b:ScalarGate i=>b.bound j hj
end YM.WilsonCoeffUV.Bank
