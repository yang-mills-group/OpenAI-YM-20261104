import YM.RGComparison.Core16.Trajectory
import YM.Bid.Station
import YM.RGComparison.Core16.Barrier

/-! Forest independence of the actual signed, unnormalized transfer and of
its genuine conditional quotient, at every group-valued retained field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorForestHaar

open Lattice RG Tree Wilson RGComparison.Core16 RGComparison.Core16.Descent
variable {G : Gauge} {A : Levels G} {m N p : ℕ} (T T' : Slices A p) (hm : m ≤ N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem outputs (β : ℕ → ℝ) (f : Config G (A.S.side N p) → E) :
    (traversal T hm).output β f=(traversal T' hm).output β f := by
  induction hm using Nat.decreasingInduction generalizing β with
  | self => rw [traversal_self,traversal_self]
  | of_succ m hm ih => rw [traversal_push T hm,traversal_push T' hm,output_push,output_push,ih]

theorem conditioned (β : ℕ → ℝ) (f : Config G (A.S.side N p) → E) (U : Config G (A.S.side m p)) :
    (traversal T hm).conditioned β f U=(traversal T' hm).conditioned β f U := by
  simp only [Descent.conditioned,Descent.vacuum,Descent.weighted,traversal_depth,outputs T T' hm]

theorem one {c f : Side} (S : StepData c f) (F F' : Forest S.ratio) (β : ℕ→ℝ)
    (O : Config G f→E) (U : Config G c) :
    (Descent.push S F (Descent.nil (top:=f))).conditioned β O U =
    (Descent.push S F' (Descent.nil (top:=f))).conditioned β O U := rfl

/-- One lower scale buys the geometric room for every larger scale and all
physical periods; the finite torus does not have to be chosen first. -/
theorem ready (H : History G) : ∀ᶠ k : ℕ in Filter.atTop, ∀ i≥k, ∀ n : ℕ,
    Bid.Larger (G:=G) (H.levels.clock.op i n) := by
  let J:=H.levels.clock.J
  let D:=fun m=>(H.S.denominator m).val
  let a (m p:ℕ):=(H.S.side m p).val
  let L m:=(H.S.block m).val
  have hd (m p:ℕ) : D m≤a m p := Nat.le_mul_of_pos_left _ (H.S.period p).pos
  have he (m p) : a (m+1) p=a m p*L m := (H.levels.clock.op m p).sizes
  have hJ m : J (m+1)≤J 0+(m+1) := by
    induction m with
    | zero => exact H.levels.fits.stepSlow 0
    | succ m ih => have hv : J (m+1+1)≤J (m+1)+1:=H.levels.fits.stepSlow _; omega
  have hL m : 3≤L m:=H.S.block_large m
  have hK m : D (m+1)=D m*L m:=PNat.mul_coe ..
  have hP m : 1+m^2≤D m := by
    induction m with
    | zero => exact le_of_eq rfl
    | succ m ih => rw [hK]; have hx:=Nat.mul_le_mul ih (hL m); nlinarith
  filter_upwards [Filter.eventually_ge_atTop (100*(J 0+9))] with k hk m km p
  have hlarge:=hk.trans km
  refine ⟨(H.levels.blocks m p).branches,?_,?_⟩
  · change 100*((J (m+1)+3)*L m+4*L m)≤a (m+1) p
    rw [he,←add_mul,←mul_assoc]
    apply Nat.mul_le_mul_right
    have side:=(hP m).trans (hd m p)
    have slow:=hJ m
    nlinarith
  exact lt_of_lt_of_le (show 1<1+m^2 by nlinarith) ((hP m).trans (hd m p))

theorem room (H : History G) : ∀ᶠ k : ℕ in Filter.atTop, ∀ j≥k, ∀ (N : ℕ) (hm : j ≤ N), ∀ n,
    ∀ T : Slices H.levels n, (traversal T hm).Room G := by
  filter_upwards [ready H] with k deep j kj N hm n T
  induction hm using Nat.decreasingInduction with
  | self => rw [traversal_self]; trivial
  | of_succ m hm ih =>
    rw [traversal_push T hm]
    exact ⟨deep m kj n,ih (kj.trans (Nat.le_succ _))⟩

/-- Prescribe just one physical forest, inside the given full history. -/
def replace {n : ℕ} (T : Slices A n) (i : ℕ) (F : Forest (A.clock.op i n).ratio) : Slices A n :=
  Function.update T i F

theorem here {n : ℕ} (T : Slices A n) (i : ℕ) (F : Forest (A.clock.op i n).ratio) :
    replace T i F i=F := Function.update_self ..

theorem elsewhere {n : ℕ} (T : Slices A n) (i : ℕ) (F : Forest (A.clock.op i n).ratio) (l : ℕ) (ne:l≠i) :
    replace T i F l=T l := Function.update_of_ne ne ..

/-- Turn the *actual* choices at all and only the nonempty steps into the
formal descent's tags, before its chart or source is evaluated. -/
def tags {k j N n : ℕ} (T : Slices A n) (choose : ∀ t, k≤t → t<N → (A.clock.op t n).Choices)
    (hj : j≤N) (kj : k≤j) : (traversal T hj).Tags := by
  induction hj using Nat.decreasingInduction with
  | self => rw [traversal_self]; exact ()
  | of_succ m hm ih =>
    rw [traversal_push T hm]
    exact (choose m kj hm,ih (kj.trans (Nat.le_succ _)))

end YM.Integration.WilsonConditionalTaylorForestHaar
end

