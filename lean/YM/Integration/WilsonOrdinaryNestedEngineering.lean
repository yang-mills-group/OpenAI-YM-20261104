import YM.Integration.WilsonCenteredNestedPhysical

/-! Exact engineering factors on every finite public OPE tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedEngineering
open Function Table OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree WilsonCenteredNestedRates
open scoped Classical BigOperators

/-- The dimension spent by each original literal leaf at its own parent. -/
theorem leaf_product (t : Tree) (s : t.Inner→ℝ) (d : t.Leaf→ℕ) (a : ℝ)
    (ap : 0<a) (layout : t.Tapered a 1 s) :
    leaves t s d a = a^(-(∑i:t.Leaf,(d i:ℝ))) *
      ∏u:t.Inner,(t.ratios a s u)^(-t.headSum (fun i=>(d i:ℝ)) u) := by
  induction t generalizing a with
  | bud =>
    change (a^(d ()))⁻¹=a^(-(∑i:Unit,(d i:ℝ))) * ∏u:Empty,_
    rw [Fintype.sum_unique,Fintype.prod_empty,mul_one,Real.rpow_neg ap.le,Real.rpow_natCast]
  | fork n f ih =>
    let r:=s (.inl ())
    let σ:=∑i:(fork n f).Leaf,(d i:ℝ)
    let μ:=fun i:Fin n=>∑j:(f i).Leaf,(d ⟨i,j⟩:ℝ)
    let β:=fun (i:Fin n) (u:(f i).Inner)=>((f i).ratios r (childAge i s) u)^
      (-(f i).headSum (fun j=>(d ⟨i,j⟩:ℝ)) u)
    have hp:0<r:=layout.1
    have sum : ∑i:Fin n, μ i = σ := Tree.sum_wages_fork (w:=fun i=>(d i:ℝ))
    have unite : (∏i:Fin n,r^(-μ i))=r^(-σ) := by
      rw [←Real.rpow_sum_of_pos hp,Finset.sum_neg_distrib,sum]
    have sub (i:Fin n) : leaves (f i) (childAge i s) (childWages i d) r =
        r^(-μ i) * ∏u:(f i).Inner,β i u :=
      ih i _ _ _ hp (by simpa only [mul_one] using layout.2.2 i)
    rw [leaves,Tree.prod_inner]
    change (∏i:Fin n, leaves (f i) (childAge i s) (childWages i d) r) =
      a^(-σ)*((r/a)^(-σ)*∏i:Fin n,∏u:(f i).Inner,β i u)
    simp_rw [sub]
    rw [Finset.prod_mul_distrib,unite,Real.div_rpow hp.le ap.le]
    field_simp [(Real.rpow_pos_of_pos ap (-σ)).ne']

theorem root {n : ℕ} {p : Fin n→Tree} (v : (fork n p).Leaf→ℕ)
    (s : (fork n p).Inner→ℝ) (h : ℕ) {a : ℝ} (layout : (fork n p).Tapered a 1 s) :
    (s (.inl ()))^h * leaves (fork n p) s v (s (.inl ())) =
      toll (fun i=>(v i:ℝ)) 0 h s := by
  let t:=fork n p
  let r:=s (.inl ())
  have hp:0<r:=layout.1
  have legal : t.Tapered r 1 s:=⟨hp,by simp [r],layout.2.2⟩
  rw [leaf_product _ _ _ _ hp legal,Tree.prod_inner]
  unfold Tree.toll
  change r^h*(r^(-(∑i:t.Leaf,(v i:ℝ)))*
    ((r/r)^(-(∑i:t.Leaf,(v i:ℝ)))*∏i:Fin n,∏u:(p i).Inner,_))=_
  rw [div_self hp.ne',Real.one_rpow,one_mul]
  simp only [sub_zero]
  rw [Fintype.prod_sigma]
  rw [←mul_assoc,←Real.rpow_natCast,←Real.rpow_add hp]
  rfl

/-- Isolate every arbitrary-power loss on exactly its own geometric ratio. -/
theorem loss {n : ℕ} {p : Fin n→Tree} (v : (fork n p).Leaf→ℝ)
    (s : (fork n p).Inner→ℝ) (ε h : ℝ) {a : ℝ} (layout : (fork n p).Tapered a 1 s) :
    toll v ε h s = toll v 0 h s * ∏u:(fork n p).Inner,((fork n p).ratios 1 s u)^(-ε) := by
  rw [←Tree.toll_eq layout.1,←Tree.toll_eq layout.1]
  unfold Tree.scaleFee
  simp only [sub_zero]
  rw [mul_assoc,←Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun u _=>by
    rw [← Real.rpow_add (layout.pricePositive 1 one_pos u),sub_eq_add_neg]

end YM.Integration.WilsonOrdinaryNestedEngineering
