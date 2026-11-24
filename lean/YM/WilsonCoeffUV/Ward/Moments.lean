import YM.WilsonCoeffUV.Ward.FromPeriods
/-!
# Width after grouping by root to Laurent and momentum moments. Polynomial
probes (shift-stable). -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{I α V : Type*}{k r:ℕ}{s t A B : ℝ}

-- choose artifact cost
lemma roll_poly (k:ℕ)(h:0<s): ∃ C:ℝ,0<C ∧∀ x:ℕ, (1+x:ℝ)^k≤ C*Real.exp (s*x):= by
   induction k generalizing s with
   | zero=> exact ⟨1, one_pos, fun x=> by rw [pow_zero,one_mul]; exact Real.one_le_exp (by positivity)⟩
   | succ k ih=>
     obtain ⟨C,hc,hC⟩:= ih (s:=s/2) (by positivity)
     have he : 0<s/2:= by positivity
     refine ⟨C*(1+(s/2)⁻¹),by positivity,fun x=>?_⟩
     let E:=Real.exp (s/2*x)
     have hx : (x:ℝ)≤(s/2)⁻¹*E:= (le_inv_mul_iff₀ he).mpr (by unfold E; linarith only [Real.add_one_le_exp (s/2*x)])
     have hy : 1+(x:ℝ) ≤ (1+(s/2)⁻¹)*E:= by rw [add_mul,one_mul]; exact add_le_add (Real.one_le_exp (by positivity)) hx
     rw [pow_succ]; refine (mul_le_mul (hC _) hy (by positivity) (by positivity)).trans_eq ?_
     unfold E; rw [mul_mul_mul_comm, ←Real.exp_add]; congr 2; ring

def ceilPoly (k:ℕ)(s:ℝ) := if h:0<s then (roll_poly k h).choose else 1
lemma ceilPoly_pos (k:ℕ)(s:ℝ):0<ceilPoly k s:=by
  unfold ceilPoly; split
  next h=> exact (roll_poly k h).choose_spec.1
  next h=> exact one_pos
lemma ceilPoly_use (k:ℕ)(h:0<s)(x:ℕ): (1+x:ℝ)^k ≤ceilPoly k s*Real.exp (s*x):= by rw [ceilPoly, dif_pos h]; exact (roll_poly k h).choose_spec.2 x
lemma poly_used (k:ℕ)(h:t<s)(x:ℕ): (1+x:ℝ)^k*Real.exp (-s*x) ≤ ceilPoly k (s-t)*Real.exp (-t*x):= by
   let he:= ceilPoly_use k (sub_pos.mpr h) x
   refine (mul_le_mul_of_nonneg_right he (by positivity : 0≤Real.exp _)).trans_eq ?_
   rw [mul_assoc, ← Real.exp_add]; congr 2; ring

section root
variable [Fintype α] [NormedAddCommGroup V]{F:Ten V (Cloth α) (k+1)}
-- Weighted sum with one leg fixed. The other legs may form an empty list.
def cent (x:Cloth α)(F:Ten V (Cloth α) (k+1))(r:ℕ)(t A:ℝ) := SumBudget (fun y : dock Cover α k=> let w := Fin.cons x y; ((1+(soar terrain w):ℝ)^r*Real.exp (t*soar terrain w))*‖F w‖) A
lemma cent_amber (h:Amber terrain s A F)(he:t<s)(x:Cloth α)(r:ℕ) : cent x F r t ((A*ceilPoly r ((s-t)/2))*tiePay α k ((s-t)/2)) := by
   set u := (s-t)/2; have hu:0<u:=by unfold u; linarith
   have H (y: dock Cover α k): let w :Fin (k+1) → Cloth α:=Fin.cons x y; let l:=soar terrain w
                                ((1+l:ℝ)^r*Real.exp (t*l))*‖F w‖ ≤ (A*ceilPoly r u)*Real.exp (-u*l):= by
      intro w l; have hc : 0< ceilPoly r u:=ceilPoly_pos ..
      have hz:= h.2 w; have hb:= h.1
      calc
       _ ≤ (ceilPoly r u*Real.exp (u*l)*Real.exp (t*l))*(A*Real.exp (-s*l)) := mul_le_mul (mul_le_mul_of_nonneg_right (ceilPoly_use r hu l) (by positivity)) hz (by positivity) (by positivity)
       _ = (A*ceilPoly r u)*(Real.exp ((u*l+t*l)+ -s*l)):=by rw [Real.exp_add,Real.exp_add]; ring
       _ = _ := by unfold u; congr 2; ring
   have hp : 0≤A*ceilPoly r u:=mul_nonneg h.1 (ceilPoly_pos ..).le
   have hr (y:dock Cover α k): Real.exp (-u*soar terrain (Fin.cons x y))≤ sail (u/k) terrain x.1 y := by
     by_cases he:k=0
     · subst k; simp [sail,soar,league, terrain]
     have he' j : terrain.gap x.1 (y j).1 ≤ soar terrain (Fin.cons x y):= leg_le terrain (Prod.fst ∘ (Fin.cons x y : Fin (k+1)→Cloth α)) 0 (Fin.succ j)
     simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero, one_mul] using sail_cut (d:=terrain) (Nat.zero_le (soar terrain (Fin.cons x y))) le_rfl hu (by omega) x.1 y he'
   apply budget_minor (cap_scale ?h hp) (fun _=>mul_nonneg (mul_nonneg (by positivity) (by positivity)) (norm_nonneg _)) (fun i=> le_trans (H i) (mul_le_mul_of_nonneg_left (hr i) hp))
   case h=> by_cases he:k=0
            · subst k; simp [sail,SumBudget,tiePay]; exact summable_of_hasFiniteSupport (Set.toFinite _)
            exact train_pay (by exact div_pos hu (Nat.cast_pos.mpr (by omega))) _ _
-- norm remains valid after shifting root, convert consumers later
end root

-- polynomial functions charged on Cover

def broad (f:Cover→ℝ) := ∃ k:ℕ, ∃ C:ℝ,0≤C ∧ ∀ x:Cover, |f x| ≤C*(1+size x:ℝ)^k
def chalk (i : Axis) (x:Cover): ℝ:= x i
lemma broad.const (a:ℝ): broad fun _=>a:= ⟨0,|a|,abs_nonneg _, fun _=> by simp⟩
lemma broad.one : broad 1:= broad.const 1
lemma chalk_fee (i:Axis)(x:Cover): |chalk i x|≤ size x := by
    rw [chalk,← Int.cast_abs,←Int.natCast_natAbs, Int.cast_natCast]; exact_mod_cast own_size x i
lemma broad.chalk (i:Axis): broad (chalk i):= ⟨1,1,zero_le_one,fun x=> by rw [pow_one,one_mul]; linarith only [chalk_fee i x]⟩
lemma broad.add {f g:Cover→ℝ}(a:broad f)(b:broad g): broad (f+g):= by
    obtain ⟨k,C,h,hp⟩:=a; obtain ⟨j,D,h',hf⟩:=b; refine ⟨k+j,C+D,add_nonneg h h',fun i=>?_⟩
    rw [add_mul,Pi.add_apply]; exact (abs_add_le ..).trans (add_le_add ((hp i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by apply le_add_of_nonneg_right; positivity) (by omega)) h)) ((hf i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by apply le_add_of_nonneg_right; positivity) (by omega)) h')))
lemma broad.mul {f g:Cover→ℝ}(a:broad f)(b:broad g): broad (f*g):= by
    obtain ⟨k,C,h,hp⟩:=a; obtain ⟨j,D,h',hf⟩:=b; refine ⟨k+j,C*D,mul_nonneg h h',fun i=>?_⟩
    rw [Pi.mul_apply,abs_mul]; refine (mul_le_mul (hp i) (hf i) (abs_nonneg _) (by positivity)).trans_eq ?_
    rw [mul_mul_mul_comm,pow_add]
lemma broad.neg {f}(h:broad f):broad (-f):= by obtain ⟨k,C,h,hp⟩:=h; exact ⟨_,_,h,fun i=> by rw [Pi.neg_apply,abs_neg]; exact hp i⟩
lemma broad.sub {f g}(h:broad f)(e:broad g):broad (f-g):=by rw [sub_eq_add_neg]; exact h.add e.neg
lemma broad.around {f}(h:broad f)(x:Cover): broad fun i=> f (i+x):=by
  obtain ⟨k,C,h,hp⟩:=h
  refine ⟨k,C*(1+size x:ℝ)^k,by positivity,fun i=>(hp (i+x)).trans ?_⟩
  rw [mul_assoc,←mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) h
  have he:(size (i+x):ℝ)≤(size i:ℝ)+size x:=by exact_mod_cast size_add i x
  have hm:0≤ (size x:ℝ)*(size i):=by positivity
  linarith
lemma broad.power {f}(h:broad f)(k): broad (f^k):=by induction k with
   | zero=> rw [pow_zero]; exact broad.one
   | succ k ih=> rw [pow_succ]; exact ih.mul h

section sums
variable {d:Cover→ℝ}
-- X numerical curve
lemma sweat (h:0<s){v:Cover→ℝ}(hg:∀ i,|v i|≤A*Real.exp (-s*size i))(f:Cover→ℝ)(hp: ∀ i,|f i|≤ B*(1+size i:ℝ)^k) (he:0≤A)(hh:0≤B): SumBudget (fun i=>‖f i*v i‖) ((A*B*ceilPoly k (s/2))*sheetPay (s/2)):=by
   have ha:0≤ A*B*ceilPoly k (s/2):= mul_nonneg (mul_nonneg he hh) (ceilPoly_pos ..).le
   refine budget_minor (cap_scale (Width.compactPay _ (by positivity : 0<s/2)) ha) (fun i=> norm_nonneg _) (fun i=>?_)
   simp only [Real.norm_eq_abs, abs_mul]; refine (mul_le_mul (hp i) (hg i) (abs_nonneg _) (by positivity)).trans ?_; rw [mul_mul_mul_comm,mul_comm B A, mul_assoc (A*B)]
   apply mul_le_mul_of_nonneg_left _ (mul_nonneg he hh); convert! poly_used k (show s/2<s by linarith) (size i) using 1; congr 2; ring
lemma sweat_pay (h:0<s){v:Cover→ℝ}(hg:∀ i,|v i|≤A*Real.exp (-s*size i))(hp:broad d): Summable fun i=> d i*v i:=by
   obtain ⟨k,B,hp,H⟩:=hp; have ha:0≤A:= by have he:=hg 0; simp [size] at he; exact (abs_nonneg _).trans he
   exact (sweat h hg _ H ha hp).2.1.of_norm
lemma budget_poly {v:On Axis ℝ}(h:Width s A v)(hp:0<s)(e:broad d): Summable fun i=> d i * v i:= by
  refine sweat_pay (A:=A) hp ?_ e
  intro i; rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv]; apply (le_div_iff₀ (by positivity)).2
  rw [mul_comm]; exact cap_pt h i
end sums
end YM.WilsonCoeffUV.Bank
