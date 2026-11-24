import YM.Integration.WilsonMeasuredPathTaylor

/-! The honest Wilson-path Taylor remainder of each actual finite curvature atom at its translated root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedCurvatureRayTaylor
open Function Finset Lattice Wilson RG WilsonMeasuredPathTaylor
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {k:ℕ}

def letters (a:Atom G k) (b:Fin k→G.ColorIndex):List (WilsonSlotContactTruncation.Letter G):=
  List.ofFn fun i=>(a.leg i,b i)

def polynomial (a:Atom G k) (x:Site n) (v:Directions G n) (q:ℕ) (t:ℝ):ℂ:=
  ∑ b,(a.coeff b:ℂ)*jet (read v x (letters a b)) q t

def bill (length:ℕ) (A:ℝ) (q:ℕ) (t:ℝ):ℝ:=
  (2*(length:ℝ)*A)^(q+1)*|t|^(q+1)/(q+1).factorial

def Available (a:Atom G k) (x:Site n) (v:Directions G n) (A:ℝ):Prop:=
  ∀b:Fin k→G.ColorIndex,∀e∈WilsonSlotContactTruncation.contacts x (letters a b),speed v e≤A

theorem evaluated (a:Atom G k) (x:Site n) (v:Directions G n) (t:ℝ):
    (a.unmasked (field v t) x:ℂ)=∑b,(a.coeff b:ℂ)*read v x (letters a b) t:=by
  simp only [Atom.unmasked,Atom.poly,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun u:ℂ=>(a.coeff b:ℂ)*u)
  change (∏i:Fin k,(((a.leg i).atSite (field v t) x (b i):ℝ):ℂ)) =
    ((List.ofFn fun i=>(a.leg i,b i)).map (WilsonSlotContactTruncation.coord (field v t) x)).prod
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_apply,WilsonSlotContactTruncation.coord]

private theorem list_bound {ι:Type*} (l:List ι) (f:ι→ℝ) (A:ℝ) (h:∀e∈l,f e≤A):
    (l.map f).sum≤(l.length:ℝ)*A:=by
  induction l with
  | nil=>simp
  | cons i l ih=>
    have first:=h i (List.mem_cons_self ..)
    have tail:=ih (fun e he=>h e (List.mem_cons_of_mem _ he))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

theorem priced (a:Atom G k) (x:Site n) (v:Directions G n) {A:ℝ} (ha:0≤A) (h:Available a x v A)
    (b:Fin k→G.ColorIndex):0 ≤ score v x (letters a b) ∧ score v x (letters a b) ≤ 2*(a.length:ℝ)*A:=by
  let es:=WilsonSlotContactTruncation.contacts x (letters a b)
  have size:es.length≤2*a.length:=by
    change (WilsonSlotContactTruncation.contacts x (letters a b)).length≤2*a.length
    rw [WilsonSlotContactTruncation.length_contacts]
    simp only [letters,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Atom.length,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _=>by change (a.leg i).length+(a.leg i).walk.length≤2*(a.leg i).length;unfold Slot.length;omega
  have positive (s:List (Edge (Site n))):0≤(s.map (speed v)).sum:=by
    induction s with
    | nil=>simp
    | cons i l ih=>exact add_nonneg (norm_nonneg _) ih
  refine ⟨positive es,(list_bound es (speed v) A (h b)).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast size) ha

theorem original (a:Atom G k) (x:Site n) (v:Directions G n) {A:ℝ} (ha:0≤A) (h:Available a x v A)
    (q:ℕ) (t:ℝ):‖(a.unmasked (field v t) x:ℂ)-polynomial a x v q t‖≤a.magnitude*bill a.length A q t:=by
  rw [evaluated,polynomial,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑b,|a.coeff b| * bill a.length A q t:=by
      apply Finset.sum_le_sum
      intro b _
      rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (WilsonMeasuredPathTaylor.slots v x (letters a b) q t).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (priced a x v ha h b).1 (priced a x v ha h b).2 _) (by positivity)) (by positivity))
    _ = _:=by rw [Atom.magnitude,Finset.sum_mul]

theorem masked (a:Atom G k) (x:Site n) (v:Directions G n) {A:ℝ} (ha:0≤A) (h:Available a x v A)
    (q:ℕ) (t τ:ℝ) (W:Support n):
    ‖(RG.masked τ W (fun U=>a.unmasked U x) (field v t):ℂ)-
      RG.masked τ W (fun _=>polynomial a x v q t) (field v t)‖≤a.magnitude*bill a.length A q t:=by
  by_cases live:Healthy τ W (field v t)
  · rw [masked_eq _ _ _ _ live,masked_eq _ _ _ _ live]
    exact original a x v ha h q t
  · rw [masked_ne _ _ _ _ live,masked_ne _ _ _ _ live]
    simp only [sub_zero,norm_zero]
    unfold Atom.magnitude bill
    positivity

end YM.Integration.FundedCurvatureRayTaylor
end
