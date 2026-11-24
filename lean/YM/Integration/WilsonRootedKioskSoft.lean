import YM.Integration.WilsonRootedKioskReclosure

/-! Genuine soft deposits on the two current Kiosk records. The second bound
retains the measured shifts on their own filed drawer addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskSoft
open Filter Function Finset Lattice Wilson RG Ac Marker
open Push.Corrected Push.AbsoluteSums MeasureTheory RG3 RG3.Ink Ovens Ovens.Pipes
open QuadraticLocal QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Progress.DirectedRecipe
open WilsonRootedFusionFirstJoin WilsonRootedFusionScratch WilsonRootedKioskReclosure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{p:BudgetPoint}{U W Z:Activities G n}
variable {V T ι:Type}[DecidableEq V][Countable ι]{R:Census V}{o:V → Site n}
variable {e f a b m c:ℝ}

theorem scale {I:Type*}{X:I → Support n}{w:I → ℝ}{B:ℕ}{s r l:ℝ}(pos:0 ≤ l)
    (q:Hit X B w s r):Hit X B (fun i => l*w i) s (l*r):=by
  intro x
  convert budget_scale pos (q x) using 1
  funext i
  by_cases atRoot:x∈X i <;> simp [atRoot,mul_assoc]

theorem joined {I:Type*}{X:I → Support n}{u v:I → ℝ}{B:ℕ}{s r l:ℝ}
    (q:Hit X B u s r)(q':Hit X B v s l):Hit X B (fun i => u i+v i) s (r+l):=by
  intro x
  convert budget_plus (q x) (q' x) using 1
  funext i
  by_cases atRoot:x∈X i <;> simp [atRoot,add_mul]

theorem entered {I J:Type*}{A:I → Support n}{X:J → Support n}(E:I↪J)(same:∀i,X (E i)=A i)
    {u:I → ℝ}{B:ℕ}{s l:ℝ}(q:Hit A B u s l):Hit X B (stuff E u) s l:=by
  intro y
  apply transfer_budget E _ _ (q y)
  · intro i
    simp only [stuffed,same]
  · intro j absent
    simp only [blank E u absent,zero_mul,ite_self]

theorem ticket (X:Pipes G n)(d:Tap G n){B:ℕ}{s l:ℝ}(hs:0 ≤ s)(small:l ≤ 1)
    (offer:QuadraticLocal.Hard.SoftPrice X d B s l):
    ∃ q:ℕ → ℝ,(∀i,0 ≤ q i) ∧ Hit X.softer B q s (2*l) ∧
      ∀i u,|Real.exp (d.logarithm i u)-1| ≤ q i:=by
  obtain ⟨q,hq,own,paid⟩:=offer.funds
  refine ⟨fun i=>2*q i,fun i => mul_nonneg zero_le_two (hq i),scale zero_le_two paid,?_⟩
  intro i u
  obtain ⟨x,hx⟩:=X.sites i
  have one:=Samples.one_le_quote (paid x) i
  rw [if_pos hx] at one
  have qi:q i ≤ l:=(le_mul_of_one_le_right (hq _) (Real.one_le_exp (mul_nonneg hs (by positivity)))).trans one
  exact (Real.abs_exp_sub_one_le ((own i u).trans (qi.trans small))).trans
    (mul_le_mul_of_nonneg_left (own i u) zero_le_two)

private theorem scalar (w:V → ℝ)(x:ℝ):Poly.price w (Poly.send R.quiet (x:ℂ))=|x|:=by
  rw [Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real,Real.norm_eq_abs]

variable (H:QuadraticLocal.Hard T p U.forced U.K o R)
variable (D:Kiosk.First p U W e f b)(D₂:Kiosk.Second p W Z f m a c)
variable (M:Canopy.ShiftRows T ι G p o R)

theorem first (w:V → ℝ)(hb:0 ≤ b+1):
    ∃ q:ℕ → ℝ,(∀i,0 ≤ q i) ∧ Hit D.skeleton.softer p.B q (b+1) (2*D.mainly) ∧
      ∀t i u,Poly.price w ((incumbent H D t).ink (.inr i) u) ≤ q i:=by
  obtain ⟨q,hq,pays,values⟩:=ticket D.skeleton D.tap hb D.funds.soft_limit D.softPaid
  refine ⟨q,hq,pays,?_⟩
  intro t i u
  exact (scalar w (Real.exp (D.tap.logarithm i u)-1)).le.trans (values i u)

theorem second (w:V → ℝ)(hw:∀v,0<w v)(ha:0 ≤ a+1)(shipment:M.Budget w p.B (a+1) c):
    ∃ q:ℕ → ℝ,(∀i,0 ≤ q i) ∧ Hit (drawer G n).softer p.B q (a+1) (2*(D₂.mainly+c)) ∧
      ∀t i u,Poly.price w ((located H D D₂ M t).ink (.inr i) u) ≤ q i:=by
  obtain ⟨s,hs,priced⟩:=shipment.earned
  have cpos:=budget_nonneg (priced 0)
  obtain ⟨q,hq,fin,hcash⟩:=ticket D₂.skeleton D₂.tap ha ((le_add_of_nonneg_right cpos).trans D₂.funds.soft_limit) D₂.softPaid
  let first:=stuff (Rack.upS D₂.skeleton) q
  let extra:=stuff M.packPost (fun i=>Poly.price w (s i))
  have qb:Hit (drawer G n).softer p.B first (a+1) (2*D₂.mainly):=entered _ (Rack.soft_up _) fin
  have sb:Hit (drawer G n).softer p.B extra (a+1) c:=entered _ M.packSite priced
  have widened (i:ℕ)(u:Config G n):|Real.exp ((Rack.widen D₂.skeleton D₂.tap).logarithm i u)-1| ≤ first i:=by
    by_cases present:i∈Set.range (Rack.upS D₂.skeleton)
    · obtain ⟨k,rfl⟩:=present
      simpa only [Rack.widen,first,stuffed] using hcash k u
    · simp [Rack.widen,first,blank _ _ present]
  have placed (t:T)(i:ℕ)(u:Config G n):Poly.price w (M.placed t i u) ≤ extra i:=by
    by_cases present:i∈Set.range M.packPost
    · obtain ⟨k,rfl⟩:=present
      simpa only [Canopy.ShiftRows.placed,extra,stuffed] using (hs k t u).reprice w hw
    · simp [Canopy.ShiftRows.placed,extra,blank _ _ present]
  refine ⟨fun i=>first i+extra i,fun i => add_nonneg (Rack.positive _ _ hq i)
    (Rack.positive _ _ (fun k=>Poly.nonnegative hw (s k)) i),?_,?_⟩
  · intro x
    exact budget_loosen (joined qb sb x) (by linarith)
  · intro t i u
    change Poly.price w (Poly.send R.quiet ((Real.exp ((Rack.widen D₂.skeleton D₂.tap).logarithm i u)-1:ℝ):ℂ)+M.placed t i u) ≤ _
    exact (Poly.addition hw ..).trans (add_le_add ((scalar w _).le.trans (widened i u)) (placed t i u))
end YM.Integration.WilsonRootedKioskSoft
