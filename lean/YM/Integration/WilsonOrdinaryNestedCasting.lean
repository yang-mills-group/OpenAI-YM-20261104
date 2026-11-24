import YM.Integration.WilsonOrdinaryNestedEngineering

/-! Engineering telescopes for each individual choice of the retained output
at every vertex, before summing over the physical reader's channels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedCasting
open OPE.Nesting OPE.Nesting.Tree WilsonCenteredNestedRates WilsonOrdinaryNestedEngineering
open scoped Classical BigOperators

def head : (t:Tree)→(t.Leaf→ℕ)→(t.Inner→ℕ)→ℕ
  | bud,d,_=>d ()
  | fork _ _,_,e=>e (.inl ())

def product : (t:Tree)→(t.Inner→ℝ)→(t.Leaf→ℕ)→(t.Inner→ℕ)→ℝ
  | bud,_,_,_=>1
  | fork _ p,s,d,e=>
     (s (.inl ())^(e (.inl ())) / ∏i,s (.inl ())^(head (p i) (childWages i d) (childAge i e))) *
        ∏i,product (p i) (childAge i s) (childWages i d) (childAge i e)

theorem telescope (t:Tree) (s:t.Inner→ℝ) (d:t.Leaf→ℕ) (e:t.Inner→ℕ) (a:ℝ)
    (ap:0<a) (layout:t.Tapered a 1 s) :
    product t s d e =
      a^(head t d e)*leaves t s d a*∏u:t.Inner,(t.ratios a s u)^(e u) := by
  induction t generalizing a with
  | bud =>
    change 1=a^(d ())*((a^(d ()))⁻¹)*∏u:Empty,_
    rw [Fintype.prod_empty,mul_one,mul_inv_cancel₀ (pow_ne_zero _ ap.ne')]
  | fork n f ih =>
    let r:=s (.inl ())
    let m:=e (.inl ())
    let k (i:Fin n):=head (f i) (childWages i d) (childAge i e)
    let W (i:Fin n):=leaves (f i) (childAge i s) (childWages i d) r
    let G (i:Fin n):=∏v:(f i).Inner,((f i).ratios r (childAge i s) v)^(childAge i e v)
    have rp:0<r:=layout.1
    have sub (i:Fin n) : product (f i) (childAge i s) (childWages i d) (childAge i e) =
        r^(k i)*W i*G i:=ih i _ _ _ r rp (by simpa only [mul_one] using layout.2.2 i)
    rw [product,Tree.prod_inner]
    simp_rw [sub]
    change (r^m/(∏i:Fin n,r^(k i)))*(∏i:Fin n,r^(k i)*W i*G i) =
      a^m*(∏i:Fin n,W i)*((r/a)^m*∏i:Fin n,G i)
    simp only [Finset.prod_mul_distrib,div_pow]
    have ne:(∏i:Fin n,r^(k i))≠0:=Finset.prod_ne_zero_iff.mpr fun i _=>pow_ne_zero _ rp.ne'
    field_simp [ne]

theorem original {n:ℕ} {f:Fin n→Tree} (s:(fork n f).Inner→ℝ)
    (d:(fork n f).Leaf→ℕ) (e:(fork n f).Inner→ℕ) {a:ℝ} (layout:(fork n f).Tapered a 1 s) :
    product (fork n f) s d e =
      Tree.toll (fun i=>(d i:ℝ)) 0 (e (.inl ())) s *
        ∏u:Σi:Fin n,(f i).Inner,((fork n f).ratios 1 s (.inr u))^(e (.inr u)) := by
  let r:=s (.inl ())
  have rp:0<r:=layout.1
  have ok:(fork n f).Tapered r 1 s:=⟨rp,by simp [r],layout.2.2⟩
  rw [telescope _ _ _ _ r rp ok,head,WilsonOrdinaryNestedEngineering.root _ _ _ layout,Tree.prod_inner]
  change _ * ((r/r)^_ * _) = _
  rw [div_self rp.ne',one_pow,one_mul,Fintype.prod_sigma]
  rfl

end YM.Integration.WilsonOrdinaryNestedCasting
