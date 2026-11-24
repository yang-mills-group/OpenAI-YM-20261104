import YM.Integration.WilsonMarkedIndependentReporterMove

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentReporterFinance
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
open PowerSeries
variable {G:Gauge}{e:ℕ}{E W V:Credit}

private theorem powers (G:Gauge)(e:ℕ)(E:Credit):
    ∃C:Credit,∀ t:WindowS G (e+1) E,∀ i j:ℕ,i ≤ e → j ≤ e →
      let B n:=relativeF t.robe.draws t.robe.paid n t.base t.span
      ‖coeff i ((B t.n)^j)‖ ≤ C.buy t.Age:=by
  let S:=(Finset.range (e+1))×ˢ(Finset.range (e+1))
  let P (k:ℕ×ℕ)(C:Credit):Prop:=∀ t:WindowS G (e+1) E,
    let B n:=relativeF t.robe.draws t.robe.paid n t.base t.span
    ‖coeff k.1 ((B t.n)^k.2)‖ ≤ C.buy t.Age
  have localPay:∀ k∈S,∃C:Credit,P k C:=by
    rintro ⟨i,j⟩ hij
    have qi:= Finset.mem_range.mp (Finset.mem_product.mp hij).1
    let F (t:WindowS G (e+1) E)(n):=relativeF t.robe.draws t.robe.paid n t.base t.span
    obtain ⟨d,C,_,paid⟩:=clipped_pow (WindowS.payments G (e+1) E) (i:=i)
      (p:=fun t:WindowS G (e+1) E=>F t t.n) (q:=fun t:WindowS G (e+1) E=>F t t.N)
      j (fun l hl=>ascend G (e+1) l E (by omega))
    refine ⟨⟨d,max 1 C,le_max_left ..⟩,fun t=>?_⟩
    exact (paid t).main.trans (mul_le_mul_of_nonneg_right (le_max_right ..)
      (pow_nonneg (zero_le_one.trans t.warm) _))
  obtain ⟨C,h⟩:=uniformPays (P:=P) S localPay
    (fun i _ _ _ le paid t=>(paid t).trans (le _ t.warm))
  exact ⟨C,fun t i j hi hj=>h (i,j) (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩) t⟩

/-- The two actual adjacent endpoints, the one retained ratio and the fixed matrix order
determine the price before the common upper cutoff is chosen. -/
theorem adjacent (H:Hol G)(P:SealR G)(e:ℕ)(E W V:Credit):
    ∃C:Credit,∀ U:ChorusLine H P.ans P.path e E W V,∀ b N:ℕ,
      U.arch.V.anchor ≤ b → b < N → ∀ X:P.Rider,∀ x:ℝ,0 ≤ x → sprouted P X e x →
      let R:=U.arch.V
      let z:=Compar R.draws.S R.y b (b+1)
      sprouted P (lay R.draws R.paid P.ans P.path N b X) e (C.buy z*x):=by
  obtain ⟨Q,read⟩:=powers G e E
  let D:=robePort H P.ans P.path e E W V
  let F:ℝ:=((Fintype.card (Alma P.F):ℝ)*(e+1)^2)*4
  refine ⟨(pur F).prodC (D.prodC Q),fun U b N live fine X x hx hX=>?_⟩
  intro R z
  let I:WindowS G (e+1) E:=⟨R,b,1,N,N,b+1,live,le_rfl,fine,fine⟩
  have az:I.Age=z:=by simp [I,z,Compar,WindowS.Age]
  have z1:1 ≤ z:=az ▸ I.warm
  let M:=D.buy z
  let K:=Q.buy z
  let T:ℝ:=(e+1:ℕ)*(2*K*1)
  let r:=ratioHigh R.draws R.paid N b
  let J:=Jacob R.draws R.paid P.ans P.path N b
  have m0:0 ≤ M:=zero_le_one.trans (D.purchase z1)
  have k0:0 ≤ K:=zero_le_one.trans (Q.purchase z1)
  have t0:0 ≤ T:=by dsimp [T]; positivity
  have jm i (hi:i ≤ e) (s t:Alma P.F):twain M 0 (lineS J i s t) (lineS J i s t):=by
    apply twain.one _ _ le_rfl
    have le:= (opening (L:=U) live (v:=Nat.lt_succ_self b) (h0:=fine) (pM:=fine) s t hi).main
    exact le.trans (D.elder (R.depth _ live) (az ▸ I.covers (j:=0) (Nat.zero_le _)))
  have pk i j (a:i ≤ e)(b':j ≤ e):twain K 0 (coeff i (r^j)) (coeff i (r^j)):=by
    apply twain.one _ _ le_rfl
    have hp:=read I i j a b'
    simpa only [I,relativeF,palmB,Nat.add_zero,chart_one,az,r,K] using hp
  have small i (hi:i ≤ e) (j:Alma P.F):
      twain (T*x) 0 (coeff i (music r X j)) (coeff i (music r X j)):=by
    apply musicFund r r K 1 x hx k0 zero_le_one le_rfl pk X X _ i hi j
    intro l hl k
    rw [one_mul]
    exact twain.one _ _ le_rfl (hX l hl k)
  intro i hi j
  have out:=(cargo_rise J J M T x hx m0 t0 le_rfl jm (music r X) (music r X)
    small i hi j).main
  apply out.trans
  apply mul_le_mul_of_nonneg_right _ hx
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Credit.products]
  have h:=mul_le_mul_of_nonneg_right (pure_goal F z) (mul_nonneg m0 k0)
  simpa only [F,M,K,T,Nat.cast_add,Nat.cast_one] using (by convert h using 1; dsimp [F,M,K,T]; ring)

/-- Every factor in the fee lies on the short interval between the two reports. -/
theorem interval (H:Hol G)(P:SealR G)(e:ℕ)(E W V:Credit):
    ∃C:Credit,∀ U:ChorusLine H P.ans P.path e E W V,∀ b d N:ℕ,
      U.arch.V.anchor ≤ b → b+d ≤ N → ∀ Z:ℝ,1 ≤ Z →
      (∀t<d,Compar U.arch.V.draws.S U.arch.V.y (b+t) (b+t+1) ≤ Z) →
      ∀ X:P.Rider,∀ x:ℝ,0 ≤ x → sprouted P X e x →
      let R:=U.arch.V
      sprouted P (street R.draws R.paid P.ans P.path N b d X) e
        ((C.buy Z)^d*x):=by
  obtain ⟨C,step⟩:=adjacent H P e E W V
  refine ⟨C,fun U b d=>?_⟩
  induction d with
  | zero=>
    intro N _ _ Z _ _ X x _ h
    simpa only [street_nil,pow_zero,one_mul] using h
  | succ d ih=>
    intro N live done Z z1 wages X x hx hX R
    let A:=C.buy Z
    have a0:0 ≤ A:=zero_le_one.trans (C.purchase z1)
    have here:R.anchor ≤ b+d:=live.trans (Nat.le_add_right _ _)
    have fine:b+d<N:=by omega
    let Q:=lay R.draws R.paid P.ans P.path N (b+d) X
    have rent:sprouted P Q e (A*x):=by
      intro i hi j
      apply (step U (b+d) N here fine X x hx hX i hi j).trans
      apply mul_le_mul_of_nonneg_right _ hx
      apply C.elder _ (wages d (Nat.lt_succ_self d))
      have y:=R.depth (b+d) here
      have delta:=scales R.draws.S (Nat.le_succ (b+d))
      dsimp [Compar]
      linarith
    have own:=ih N live (by omega) Z z1 (fun t ht=>wages t (by omega)) Q (A*x)
      (mul_nonneg a0 hx) rent
    rw [←Street_steal]
    simpa only [pow_succ,mul_assoc,Q,A] using own

end YM.Integration.WilsonMarkedIndependentReporterFinance
