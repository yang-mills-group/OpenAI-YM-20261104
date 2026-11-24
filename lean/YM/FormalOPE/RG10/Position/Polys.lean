import YM.FormalOPE.RG10.Position.Columns

/-!
# Global polynomial-log estimates from a one-step polynomial difference
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J:Type*}{X:Type*}[NormedAddCommGroup X]

def Polys (f:ℝ→X) := ∃ d:ℕ, ∃ C:ℝ,0 ≤ C ∧ ∀ x:ℝ, ‖f x‖≤ C*(1+|x|)^d
namespace Polys
variable {x y:ℝ}{f g:ℝ→ X}
-- cost operations on slots real or complex
lemma rise (x:ℝ) : 1 ≤ 1+ |x|:=by simp
lemma stretch (h:Polys f): Polys (fun x=>f (-x)):=by obtain ⟨d,C,hc,hu⟩:=h; exact ⟨d,C,hc,fun x=> by simpa using hu (-x)⟩
lemma const (x:X): Polys (fun _=>x):= ⟨0,‖x‖,norm_nonneg _,by simp⟩
private lemma maxPower (hx : Polys f)(hy : Polys g):∃ d:ℕ,∃ C:ℝ,0 ≤ C ∧ (∀ x:ℝ, ‖f x‖≤ C*(1+|x|)^d) ∧ (∀ x:ℝ, ‖g x‖≤ C*(1+|x|)^d) := by
 obtain ⟨d,M,h,he⟩:=hx; obtain ⟨e,N,h',he'⟩:=hy;
 exact ⟨max d e, max M N,h.trans (le_max_left ..),fun x=>(he x).trans (mul_le_mul (le_max_left ..) (pow_le_pow_right₀ (rise _) (le_max_left ..)) (by positivity) (by positivity)), fun x=>(he' x).trans (mul_le_mul (le_max_right ..) (pow_le_pow_right₀ (rise _) (le_max_right ..)) (by positivity) (by positivity))⟩

lemma minus (h:Polys f):Polys (fun x=> -f x):=by obtain ⟨d,C,hc,hu⟩:=h; exact ⟨d,C,hc,fun x=>by rw [norm_neg]; exact hu x⟩
lemma added (h:Polys f)(k:Polys g): Polys (fun i=>f i+g i):= by obtain ⟨d,M,he,hf,hg⟩:= maxPower h k;
                                                                     exact ⟨d,M+M,add_nonneg he he,fun i=>by rw [add_mul]; exact (norm_add_le _ _).trans (add_le_add (hf i) (hg i))⟩
lemma sub (h:Polys f)(k:Polys g): Polys (fun i=>f i-g i):= by simpa only [sub_eq_add_neg] using added h k.minus
lemma sum (f:J→ℝ→X) (s:Finset J)(h:∀ i∈s,Polys (f i)): Polys (fun p=>∑ i∈s, f i p):= by
 induction s using Finset.induction_on with
 | empty=> simpa using const (0:X)
 | insert i s hi ih=>
    simp_rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).added (ih (fun i h'=>h _ (mem_insert_of_mem h')))
section
variable {K:Type*}[NormedRing K]{f g:ℝ→K}
lemma muls (h:Polys f)(k:Polys g): Polys (fun i=>f i*g i):= by
 obtain ⟨d,C,hC,u,v⟩:= maxPower h k
 refine ⟨d+d,C*C,by positivity,fun x=> (norm_mul_le ..).trans ((mul_le_mul (u x) (v x) (norm_nonneg _) (by positivity)).trans_eq ?_)⟩
 rw [pow_add]; ring
lemma power (h:Polys f)(n:ℕ):Polys (fun x=> f x^n):=by
 induction n with
 | zero=> simpa using const (1:K)
 | succ n ih=> simpa only [pow_succ] using! muls ih h
end

private lemma daytime {T p B:ℝ}{n:ℕ}(he:∀ x, ‖f (x+1)-f x‖≤ B*(1+|x|)^n)(hB:0≤B)(hp:0 ≤ p)(j:ℕ)(ht:p+j ≤ T): ‖f (p+j)‖ ≤ ‖f p‖ + j *(B*(1+T)^n):=by
 induction j with
 | zero=> simp
 | succ j ih=>
    rw [Nat.cast_add_one] at *; have hj:p+j≤T:=by linarith
    specialize ih hj;
    have hh : ‖f (p + (j + 1 : ℝ))‖ ≤ ‖f (p+j)‖ + B*(1+T)^n := calc
      _ = ‖(f (p+j+1)-f (p+j)) + f (p+j)‖:= by rw [sub_add_cancel,add_assoc]
      _ ≤ ‖f (p+j+1)-f (p+j)‖+‖f (p+j)‖:= norm_add_le _ _
      _ ≤ _:= by
        rw [add_comm ‖_ -_‖]; apply add_le_add_right ?_ _; apply (he (p+j)).trans; gcongr; rw [abs_of_nonneg (by positivity)]; exact hj
    linarith

def localRule (f:ℝ→X) := ∃ C:ℝ,0≤C∧ ∀ x:ℝ, |x|≤1 → ‖f x‖≤C -- bug precedence
lemma rule_of (h:Continuous f): localRule f:=by
 let K:= Set.Icc (-1 :ℝ) 1; let H:=(isCompact_Icc (α:=ℝ) (a:=(-1)) (b:=1)); -- placeholders
 obtain ⟨x,hx,H⟩:= H.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num)) h.norm.continuousOn;
 exact ⟨‖f x‖,norm_nonneg _,fun y hy=> H (abs_le.mp hy)⟩

private lemma payday (h:localRule f) {d:ℕ} {B} (hb:0 ≤ B) (he:∀ x, ‖f (x+1)-f x‖ ≤ B*(1+|x|)^d): ∃ C:ℝ,0 ≤ C ∧ ∀ x≥(0:ℝ), ‖f x‖ ≤ C*(1+|x|)^(d+1) := by
 obtain ⟨C,hC,H⟩:=h; refine ⟨C+B,by positivity,fun x hx=>?_⟩
 let n:= Nat.floor x; let p:= x - n; have hp': ↑n ≤ x:=Nat.floor_le hx
 have hN:p+n=x:=by unfold p; ring
 have hp : 0 ≤ p:= by linarith
 have hu:p ≤ 1:=by linarith [Nat.lt_floor_add_one x]
 calc
   _ = ‖f (p+n)‖:= by rw [hN]
   _ ≤ ‖f p‖ + n*(B*(1+x)^d):= daytime he hb hp n hN.le
   _ ≤ C + x*(B*(1+x)^d):= add_le_add (H p (by rw [abs_of_nonneg hp]; exact hu)) (mul_le_mul_of_nonneg_right hp' (by positivity))
   _ ≤ _:= by
     rw [abs_of_nonneg hx,add_mul]; apply add_le_add
     · exact le_mul_of_one_le_right hC (one_le_pow₀ (by linarith))
     rw [pow_succ,mul_comm x, mul_assoc]; gcongr; linarith

theorem steps (h:Continuous f)(hf:Polys (fun x=>f (x+1)-f x))(hg : Polys (fun x=>f (x-1)-f x)): Polys f:=by
 obtain ⟨m,C,hC,hf,hg⟩:= maxPower hf hg
 obtain ⟨Y,hY,hy⟩:= payday (rule_of h) hC hf
 obtain ⟨Z,hZ,hz⟩:= payday (rule_of (show Continuous (fun x:ℝ=>f (-x)) by fun_prop)) hC (d:=m) (fun x=> by simpa [sub_eq_add_neg,neg_add_rev,add_comm] using hg (-x))
 refine ⟨m+1,Y+Z,by positivity, fun x=>?_⟩
 cases le_total x 0 with
 | inl hx=> apply le_trans (show _ from ?_) (show Z*(1+|x|)^(m+1) ≤ _ from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hY) (by positivity));
             simpa using hz (-x) (by linarith)
 | inr hx=> exact (hy x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hZ) (by positivity))

end Polys
end YM.FormalOPE.RG10.Position.Grade
