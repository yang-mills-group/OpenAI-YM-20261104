import YM.Integration.OriginalJointCoverDecay

/-! Sum all finite active relative source positions and physical field
positions of the retained cover tensor. No torus volume enters the bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalJointCoverSum
open Function Finset Lattice Wilson RG FreeResolvent Gauge Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open OriginalJointCoverDecay OriginalMarkedWindingAllRoots
open scoped BigOperators Classical

variable {V α : Type} [DecidableEq V] [Fintype V] [Fintype α] [DecidableEq α]
    {n : Side} {l : ℕ} (J : Finset V)

def slots (l : ℕ) : ℝ := J.card+l+1
def spatial (α : Type) [Fintype α] (l : ℕ) (η : ℝ) :=
  let cell := sheetPay ((η/slots J l)/4)
  cell^J.card * ((Fintype.card α:ℝ)*cell)^l

omit [Fintype V] [DecidableEq α] in
theorem magnitude {η : ℝ} (hη : 0<η) (o : J) (u : Site n) :
    (∑ p : J→Site n, if p o=u then ∑ z : dock (Site n) α l,
      Real.exp (-η*(diameterAt J p z:ℝ)) else 0)  ≤  spatial J α l η := by
  let t := η/slots J l
  have rank : 0<slots J l := by unfold slots; positivity
  have ht : 0<t := div_pos hη rank
  let f (a : Site n) := Real.exp (-t*(separation u a:ℝ))
  let point (p : J→Site n) := ∏ v,f (p v)
  let field (z : dock (Site n) α l) := ∏ i,f (z i).1
  have separate (p : J→Site n) (h : p o=u) (z : dock (Site n) α l) :
      Real.exp (-η*(diameterAt J p z:ℝ)) ≤ point p * field z := by
    let A := univ.image p ∪ univ.image fun i => (z i).1
    let d := (diameterAt J p z:ℝ)
    have hu : u∈A := h ▸ mem_union_left _ (mem_image.mpr ⟨o,mem_univ _,rfl⟩)
    have dir (a : Site n) (ha : a∈A) : (separation u a:ℝ) ≤ d := by
      change (separation u a : ℝ)  ≤  ((A.sup fun v => A.sup fun b => separation v b : ℕ) : ℝ)
      exact Nat.cast_le.mpr ((le_sup (f:=fun v => separation u v) ha).trans
        (le_sup (f:=fun v => A.sup fun b => separation v b) hu))
    have roots : (∑ v : J,(separation u (p v):ℝ))  ≤  J.card*d := by
      simpa using sum_le_sum (s:=univ) (g:=fun _ : J => d) fun v _ => dir (p v)
        (mem_union_left _ (mem_image.mpr ⟨v,mem_univ _,rfl⟩))
    have labels : (∑ i : Fin l,(separation u (z i).1:ℝ))  ≤  l*d := by
      simpa using sum_le_sum (s:=univ) (g:=fun _ : Fin l => d) fun i _ => dir (z i).1
        (mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
    have D : 0 ≤ d := Nat.cast_nonneg _
    have factors : t*slots J l=η := div_mul_cancel₀ _ rank.ne'
    have net : (∑ v:J,(separation u (p v):ℝ))+(∑i:Fin l,(separation u (z i).1:ℝ))  ≤ 
        slots J l*d := by dsimp only [slots]; nlinarith
    unfold point field f
    rw [←Real.exp_sum,←Real.exp_sum,←Real.exp_add,←mul_sum,←mul_sum]
    apply Real.exp_monotone
    change -η*d  ≤  _
    nlinarith only [mul_le_mul_of_nonneg_left net ht.le,congrArg (fun v : ℝ => v*d) factors]
  have rootSum : (∑ p : J→Site n,point p)=(∑ a : Site n,f a)^J.card := by
    unfold point
    rw [←Fintype.prod_sum (fun (_:J) a => f a)]
    simp
  have fieldSum : (∑ z : dock (Site n) α l,field z)=
      ((Fintype.card α:ℝ)*(∑ a : Site n,f a))^l := by
    unfold field
    rw [series_way (fun v : Site n × α => f v.1) l,Fintype.sum_prod_type]
    simp [←mul_sum]
  have cost : (∑ a : Site n,f a) ≤ sheetPay (t/4) := host u ht
  have inc : 0 ≤ ∑ a : Site n,f a := sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc
    _  ≤  ∑ p : J→Site n,∑ z : dock (Site n) α l,point p*field z := by
      apply sum_le_sum
      intro p _
      split
      next eq => exact sum_le_sum (fun z _ => separate p eq z)
      next _ => exact sum_nonneg (fun z _ => mul_nonneg (prod_nonneg fun _ _ => (Real.exp_pos _).le)
        (prod_nonneg fun _ _ => (Real.exp_pos _).le))
    _ = (∑ p : J→Site n,point p)*(∑ z : dock (Site n) α l,field z) := by simp_rw [←mul_sum,←sum_mul]
    _  ≤  _ := by
      rw [rootSum,fieldSum]
      exact mul_le_mul (pow_le_pow_left₀ inc cost _) (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) inc)
        (mul_le_mul_of_nonneg_left cost (Nat.cast_nonneg _)) _) (by positivity)
        (pow_nonneg (sheetPay_pos _ (by positivity)).le _)

omit [Fintype V] [DecidableEq α] in
theorem signed {s w A : ℝ} (hw : w<s) (o : J) (u : Site n)
    (P : (J→Site n)→dock (Site n) α l→ℂ)
    (invoice : ∀ p z, ‖P p z‖ ≤ A*Real.exp (-s*(diameterAt J p z:ℝ))) (hA : 0 ≤ A) :
    OriginalMarkedWindingAllRoots.account (diameterAt J) (fun p z => ‖P p z‖) w o u  ≤  A*spatial J α l (s-w) := by
  have h := magnitude (l:=l) (α:=α) J (sub_pos.mpr hw) o u
  refine (le_trans ?_ (mul_le_mul_of_nonneg_left h hA))
  rw [mul_sum]
  unfold OriginalMarkedWindingAllRoots.account
  apply sum_le_sum
  intro p _
  split
  next h =>
    rw [mul_sum]
    apply sum_le_sum
    intro z _
    calc
      _  ≤  Real.exp (w*(diameterAt J p z:ℝ))*(A*Real.exp (-s*(diameterAt J p z:ℝ))) :=
        mul_le_mul_of_nonneg_left (invoice p z) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm,←Real.exp_add]; congr 2; ring
  next _ => simp

variable {G : Gauge} {D : V→ℕ} {k : V→ℕ} {e m N : ℕ} {A : ℝ}
    {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}

theorem held (X : FundedMarkedPathSelection.Input Q hm univ k D A) (hA : 0 ≤ A) (hN : m < N)
    (closed : Cloze D k Q Credit.leanC) (y : (J→Site n)→V → Cover)
    (placed : ∀ (p : J→Site n) (i:J),wrap n (y p i)=p i) (o : J) (u : Site n)
    (L : Pen D J→L[ℝ]ℂ) {i : ℕ} (hi : i ≤ e) {w : ℝ} (hw : w < Vσ Q m hm/2) :
    let s := Vσ Q m hm
    let base := FundedMarkedPathSelection.price Q k D A J m
    let P := fun (p : J→Site n) (z : Fin l→PhysicalWilsonRootedHessian.Label G n) =>
      L (plume ((FundedMarkedPathSelection.output X J N (y p)).2 i l) n z)
    OriginalMarkedWindingAllRoots.account (diameterAt J) (fun p z => ‖P p z‖) w o u  ≤ 
      (‖L‖*(base*tiePay (Hooks G) l (s/4)))*spatial J (Hooks G) l (s/2-w) := by
  let s := Vσ Q m hm
  let base := FundedMarkedPathSelection.price Q k D A J m
  have hb : 0 ≤ base := mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg hA _)
  have hz : 0 ≤ tiePay (Hooks G) l (s/4) := by
    by_cases h:l=0
    · simp [h,tiePay]
    · exact pow_nonneg (boardPay_nn (by have h' := perk hm; positivity)) _
  apply signed (α:=Hooks G) (n:=n) (l:=l) J (s:=s/2) (A:=‖L‖*(base*tiePay (Hooks G) l (s/4))) hw o u
    (fun p z => L (plume ((FundedMarkedPathSelection.output X J N (y p)).2 i l) n z)) ?_
    (mul_nonneg (norm_nonneg L) (mul_nonneg hb hz))
  intro p z
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
    (OriginalJointCoverDecay.output J (y p) X hA hN closed p (placed p) o hi z) (norm_nonneg L)).trans_eq
    (by ring))

end YM.Integration.OriginalJointCoverSum
end
