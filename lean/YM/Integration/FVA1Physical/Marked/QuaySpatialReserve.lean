import YM.Integration.FVA1Physical.Marked.QuaySpatialSum
import YM.Integration.FVA1Physical.Round2.RootedInterpolation
import YM.MSbar.Whisk.Span

/-! Price the same mixed polynomial-exponential spatial weight used by the
independent normalized Wilson columns. There is no sum over remote roots. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Labels Precision
open PhysicalNext.Repeat Push.Uniform Push.AbsoluteSums Further.LogJets
open RGComparison.Core16.Lam RGComparison.Core16.Catkin MSbar.Whisk
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side}

theorem extent_le_wordRadius (o:Site n) (w:List (Operand G n)) :
    extent (zone crest {o} w) ≤ 2*wordRadius o w := by
  have rad {y:Site n} (h:y∈zone crest {o} w) : separation o y ≤ wordRadius o w := by
    rcases mem_union.mp h with h|h
    · rw [mem_singleton.mp h];simp [wordRadius]
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have entry (l:List (Operand G n)) (v:Operand G n) (h:v∈l) : separation o (crest v)≤wordRadius o l := by
      induction l with
      | nil => simp at h
      | cons x xs ih =>
        change _ ≤ separation o (crest x) + wordRadius o xs
        rcases List.mem_cons.mp h with hx|hx
        · subst v; omega
        · have hh:=ih hx;omega
    exact entry w v hv
  apply yard
  intro i hi j hj
  have hi':=rad hi
  have hj':=rad hj
  rw [separation_comm o i] at hi'
  exact (separation_triangle i o j).trans (by omega)

private theorem spread_certificate (o:Site n) (w:List (Operand G n)) (s:ℕ)
    {a α:ℝ} (ha:0≤a) (pos:0<α) :
    spread crest {o} a s w ≤ (1+2*α⁻¹)^s * Real.exp ((((s:ℝ)*α)+2*a)*wordRadius o w) := by
  let v : ℝ := wordRadius o w
  have v0 : 0≤v := Nat.cast_nonneg _
  have d : (extent (zone crest {o} w):ℝ) ≤ 2*v := by unfold v;exact_mod_cast extent_le_wordRadius o w
  have e : 1≤Real.exp (α*v) := Real.one_le_exp (mul_nonneg pos.le v0)
  have f : α*v ≤ Real.exp (α*v) := by linarith only [Real.add_one_le_exp (α*v)]
  have t : v≤α⁻¹*Real.exp (α*v) := by
    calc v=α⁻¹*(α*v) := by rw [←mul_assoc,inv_mul_cancel₀ pos.ne',one_mul]
         _ ≤ _ := mul_le_mul_of_nonneg_left f (inv_nonneg.mpr pos.le)
  have p : 1+(extent (zone crest {o} w):ℝ)≤(1+2*α⁻¹)*Real.exp (α*v) := by
    nlinarith only [d,t,e]
  have ex : Real.exp (a*(extent (zone crest {o} w):ℝ))≤Real.exp ((2*a)*v) :=
    Real.exp_monotone ((mul_le_mul_of_nonneg_left d ha).trans_eq (by ring))
  apply (mul_le_mul (pow_le_pow_left₀ (by positivity : 0≤1+(extent (zone crest {o} w):ℝ)) p s) ex
    (Real.exp_pos _).le (pow_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) _)).trans_eq
  change ((1+2*α⁻¹)*Real.exp (α*v))^s*Real.exp (2*a*v)=(1+2*α⁻¹)^s*Real.exp (((s:ℝ)*α+2*a)*v)
  rw [mul_pow,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
  congr 2
  ring

theorem rooted_spread_price (o:Site n) (q s:ℕ) (z:List (Operand G n) → ℝ)
    {M a α:ℝ} (m0:0≤M) (ha:0≤a) (pos:0<α)
    (positive:∀ l,l.length=q→0≤z l)
    (bought:∀ l,l.length=q→Real.exp ((((s:ℝ)+1)*α+2*a)*wordRadius o l)*z l≤M) :
    Yarn q (fun l=>z l*spread crest {o} a s l) ≤
      (1+2*α⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost α)^q*M := by
  let Z:ℝ:=(1+2*α⁻¹)^s
  let k:=fun v:Operand G n=>Decay α o (crest v)
  have e (w : List (Operand G n)) : (w.map k).prod=Real.exp (-α*wordRadius o w) := by
    induction w with
    | nil=>simp [wordRadius]
    | cons x w ih=>
      simp only [List.map_cons,List.prod_cons,ih]
      change Real.exp (-α*separation o (crest x))*_ = Real.exp (-α*(↑(separation o (crest x)+wordRadius o w):ℝ))
      rw [←Real.exp_add,Nat.cast_add,mul_add]
  have pZ : 0≤Z := by unfold Z;positivity
  have word (w:List (Operand G n)) (hw:w.length=q) :
      z w*spread crest {o} a s w ≤ (Z*M)*(w.map k).prod := by
    rw [e]
    apply (mul_le_mul_of_nonneg_left (spread_certificate o w s ha pos) (positive w hw)).trans
    have eq : Real.exp (((s:ℝ)*α+2*a)*wordRadius o w) =
        Real.exp ((((s:ℝ)+1)*α+2*a)*wordRadius o w)*Real.exp (-α*wordRadius o w) := by
      rw [←Real.exp_add];congr 1;ring
    rw [eq]
    calc _ = (Z*(Real.exp ((((s:ℝ)+1)*α+2*a)*wordRadius o w)*z w))*Real.exp (-α*wordRadius o w) := by unfold Z;ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bought w hw) pZ) (Real.exp_pos _).le
  have paid:=shiny q word
  rw [sheen,YM.Integration.FVA1Physical.Round2.Curvature.product_word_cost] at paid
  have sites : (∑ x,k x)≤4*(Fintype.card G.ColorIndex:ℝ)*countCost α := by
    change (∑ x:(Site n×Axis)×G.ColorIndex, Decay α o x.1.1) ≤ _
    simp only [Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul]
    rw [←mul_sum,←mul_sum,show Fintype.card Axis=4 by decide]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (decay_count pos o) (Nat.cast_nonneg _))
      (show 0≤(4:ℝ) by norm_num)).trans_eq (by ring)
  apply paid.trans
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun i _=>(decay_pos ..).le) sites q)
    (mul_nonneg pZ m0)).trans_eq (by ring)

end YM.Integration.FVA1Physical.Marked
