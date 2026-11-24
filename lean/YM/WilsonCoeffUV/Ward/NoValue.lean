import YM.WilsonCoeffUV.Ward.Moments
/-!
# Gradient null identity with ordered numeric sums
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{X:Type*}

section legs
variable [AddCommGroup X][Module ℝ X]

def windsL (e:Cover)(c:G.ColorIndex){r}(T:Ten X (YForest G) (r+1)): Ten X (YForest G) r:= ∑ i:Axis,(prune T (stone (e,i) c)-prune T (stone (e-step i,i) c))

def northL (k:ℕ)(x:Cover)(a:G.Color)(T:Gen X (YForest G)) : Gen X (YForest G):= ∑ v:Axis, ∑ j:G.ColorIndex,(wickLamp a 0 (x,v) j k T+ wickLamp 0 a (x-step v,v) j k T)
lemma wick_winds (x:Cover)(c:G.ColorIndex)(P:Gen X (YForest G))(h:Pure P)(r:ℕ): northL 0 x (coatC G (Pi.single c 1)) P r=(r+1) • windsL x c (P (r+1)) := by
    let C := coatC G (Pi.single c 1)
    have he j : (C-0) j = if j=c then 1 else 0:= by rw [sub_zero]; exact Pi.single_apply ..
    have ht j: (0-C) j= - (if j=c then 1 else 0):= by rw [←he,sub_zero,zero_sub]; rfl
    unfold windsL northL; simp_rw [Finset.sum_apply,wick_beg _ _ _ _ P h,Pi.add_apply, Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single c];
    · change (C-0) _ • _+(0-C) _ • _= _; rw [he,ht]; simp [sever, sub_eq_add_neg]
    · intro j _ hh; change (C-0) _ • _ + (0-C) _ • _= _; rw [he,ht]; simp [hh]
    simp

lemma essence {P:Pal X (YForest G)}(h: vertical P)(u:∀ i,Pure (P i))(e:Cover)(c:G.ColorIndex)(k r:ℕ):
    (r+1) • windsL e c (P k (r+1))= -(∑ j∈(Finset.antidiagonal k).erase (0,k), northL j.1 e (coatC G (Pi.single c 1)) (P j.2)) r := by
     let C:= coatC G (Pi.single c 1)
     let T (j:ℕ×ℕ):= northL j.1 e C (P j.2)
     have he : ∑ i∈Finset.antidiagonal k, T i=0:=by
        unfold T northL
        rw [← h C e k, Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
     rw [← Finset.add_sum_erase _ T (show (0,k)∈_ from Finset.mem_antidiagonal.mpr (by simp))] at he
     have hg : T (0,k)= -∑ i∈(Finset.antidiagonal k).erase (0,k),T i:= eq_neg_of_add_eq_zero_left he
     have hp := wick_winds e c (P k) (u k) r; change T (0,k) r = _ at hp; rw [←hp,hg]; rfl

lemma sky_split {P:Pal X (YForest G)}(h:vertical P)(u:∀ i,Pure (P i))(e r:ℕ)(t:∀ i<e,∀ j≤ r,P i (j+1)=0)(x:Cover) (c:G.ColorIndex): windsL x c (P e (r+1))=0:=by
  -- allow no division when coefficient space Add? Module implies!
  let S:= coatC G (Pi.single c 1)
  have he := essence h u x c e r
  rw [Finset.sum_apply] at he
  have hv (j: ℕ×ℕ)(hj:j∈ (Finset.antidiagonal e).erase (0,e)): northL j.1 x S (P j.2) r=0:=by
    obtain ⟨ha,hb⟩:= Finset.mem_erase.mp hj; have hw: j.1+j.2=e:= Finset.mem_antidiagonal.mp hb
    have hh : j.1≠0:= fun h'=> ha (Prod.ext h' (show j.2=e from by omega))
    have hx (a b:G.Color)(p:Edge Cover)(i:G.ColorIndex): wickLamp a b p i j.1 (P j.2) r=0:=by
      by_cases H:j.1≤r
      · rw [wick_leg a b p i _ H]; rw [sever,t _ (by omega) _ (by omega), show prune (0:Ten X (YForest G) _) _= 0 from rfl, smul_zero, inter_zero_right, swirl_exact Smooth.zero]
      exact wick_pos _ _ _ _ _ (by omega)
    simp only [northL,Finset.sum_apply,Pi.add_apply,hx]; simp
  rw [Finset.sum_eq_zero hv,neg_zero,← Nat.cast_smul_eq_nsmul (R:=ℝ)] at he
  exact (smul_eq_zero.mp he).resolve_left (by positivity)
lemma west_floor {P:Pal X (YForest G)}(h:vertical P)(u:∀ i,Pure (P i))(hz:∀ k,P k 1=0)(e:ℕ)(x:Cover) (c:G.ColorIndex): windsL x c (P e 2)=0:=by
  -- sharper j
  let S:=coatC G (Pi.single c 1); have he := essence h u x c e 1
  rw [Finset.sum_apply] at he
  have hv (j:ℕ×ℕ)(hj:j ∈ (Finset.antidiagonal e).erase (0,e)): northL j.1 x S (P j.2) 1=0:=by
    obtain ⟨ha,hb⟩:= Finset.mem_erase.mp hj; have hw: j.1+j.2=e:= Finset.mem_antidiagonal.mp hb
    have hh : j.1≠0:= fun h'=>ha (Prod.ext h' (show j.2=e from by omega))
    have hx (a b:G.Color)(p:Edge Cover)(i:G.ColorIndex): wickLamp a b p i j.1 (P j.2) 1=0:=by
      by_cases H:j.1≤1
      · rw [wick_leg a b p i _ H, show j.1=1 from by omega, Nat.sub_self,sever, hz _, show prune (0:Ten X (YForest G) _) _= 0 from rfl, smul_zero, inter_zero_right, swirl_exact Smooth.zero]
      exact wick_pos _ _ _ _ _ (by omega)
    simp only [northL,Finset.sum_apply,Pi.add_apply,hx]; simp
  rw [Finset.sum_eq_zero hv,neg_zero,← Nat.cast_smul_eq_nsmul (R:=ℝ)] at he; exact (smul_eq_zero.mp he).resolve_left (by positivity)
end legs
section moments

variable {K:Ten ℝ (YForest G) 2} {t s A:ℝ}

def petals (K:Ten ℝ (YForest G) 2)(u:Hooks G)(i:Axis)(v:G.ColorIndex)(x:Cover) := K (Fin.cons (stone (x,i) v) ![(0,u)])
lemma petals_price (h:Amber terrain s A K)(u i v x): |petals K u i v x| ≤ A*Real.exp (-s*size x):= by
    let w : Fin 2→YForest G:= Fin.cons (stone (x,i) v) ![(0,u)]
    have he : soar terrain w=size x:=by rw [drag_two]; change size (0-x)=size x; rw [zero_sub,size_neg]
    rw [←he]; exact h.2 w

-- audit moments
def tailor (K:Ten ℝ (YForest G) 2)(w:Hooks G)(i:Axis)(v:G.ColorIndex)(f:Cover→ℝ) := ∑' x, f x * petals K w i v x
lemma tailor_add (h:Amber terrain s A K)(he:0<s)(u i j){f g:Cover→ℝ}(a:broad f)(b:broad g) : tailor K u i j (f+g)=tailor K u i j f+tailor K u i j g:=by unfold tailor; simp only [Pi.add_apply,add_mul]; exact (sweat_pay he (petals_price h _ _ _) a).tsum_add (sweat_pay he (petals_price h _ _ _) b)
lemma tailor_M (c:ℝ) (f:Cover→ℝ)(u i j): tailor K u i j (c•f)= c*tailor K u i j f:=by unfold tailor; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
lemma tailor_zero (K:Ten ℝ (YForest G) 2)(u i j): tailor K u i j 0=0:= by simp [tailor]
lemma tailor_sum (h:Amber terrain s A K)(he:0<s)(u i v)(f:Cover→ℝ)(hp:broad f): Summable fun x=>f x * petals K u i v x:=sweat_pay he (petals_price h u i v) hp
lemma petals_slide (h:Amber terrain s A K)(he:0<s)(u i v)(a:Cover)(f:Cover→ℝ)(hp:broad f): Summable fun x=> f x * petals K u i v (x-a):=by
  let T y:= f (y+a) * petals K u i v y
  have hw : Summable T:= tailor_sum h he u i v _ (hp.around a)
  refine ((Equiv.subRight a).summable_iff.mpr hw).congr ?_
  intro i; change f (i-a+a)*_= _; rw [sub_add_cancel]; rfl
def nextV (i:Axis)(f:Cover→ℝ) (x:Cover): ℝ:= f (x+step i) - f x
lemma jets_null (h:Amber terrain s A K)(he:0<s)(hc:∀ x c,windsL x c K=0)(u:Hooks G)(v:G.ColorIndex)(f: Cover→ℝ)(hp:broad f): ∑ i:Axis, tailor K u i v (nextV i f)=0 := by
   let T i x:= f x * (petals K u i v (x-step i) - petals K u i v x)
   have ht i: Summable (T i):= by simp only [T, mul_sub]; exact (petals_slide h he u i v (step i) f hp).sub (tailor_sum h he _ _ _ f hp)
   have hh (i:Axis):∑' x,T i x=tailor K u i v (nextV i f):=by
     unfold T tailor nextV; simp_rw [mul_sub,sub_mul]; rw [(petals_slide h he u i v (step i) f hp).tsum_sub (tailor_sum h he _ _ _ f hp),Summable.tsum_sub (tailor_sum h he u i v _ (hp.around _)) (tailor_sum h he u i v f hp)]; rw [← (Equiv.addRight (step (S:=ℤ) i)).tsum_eq (fun x=> f x * petals K u i v (x-step i))]; simp
   have hz (x): ∑ i:Axis,T i x=0:=by
     unfold T; rw [← Finset.mul_sum]; apply mul_eq_zero_of_right; have hv:= congr_fun (hc x v) ![(0,u)]
     simp_rw [windsL, Finset.sum_apply,Pi.sub_apply,Finset.sum_sub_distrib] at hv
     rw [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr (sub_eq_zero.mp hv).symm
   simp_rw [← hh]; rw [← Summable.tsum_finsetSum (fun _ _=> ht _),tsum_congr hz]; simp

lemma chalk_inc (i j:Axis)(x:Cover): chalk j (x+step i)=chalk j x+if i=j then 1 else 0:= by by_cases h:i=j<;> simp [h, Ne.symm, chalk]

lemma kail (h:Amber terrain s A K)(he:0<s)(hc:∀ x c,windsL x c K=0)(u:Hooks G)(v:G.ColorIndex)(i:Axis): tailor K u i v 1=0:= by
   have hx:= jets_null h he hc u v (chalk i) (broad.chalk i)
   have hg : nextV i (chalk i)=1:= funext fun x=> by simp [nextV,chalk_inc]
   rw [Finset.sum_eq_single i,hg] at hx; exact hx
   · intro j _ hj; rw [show nextV j (chalk i)=0 from funext (fun x=> by simp [nextV,chalk_inc,hj]),tailor_zero]
   simp
end moments
end YM.WilsonCoeffUV.Bank
