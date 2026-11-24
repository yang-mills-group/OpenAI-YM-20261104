import YangMills.WilsonProof.NativeSupport.JointLinearTariff
import YM.RGGapR2.Rough

/-! The two real native hats representing each complex inherited
coefficient have exactly twice its incoming rooted bill. The same hats
work at all marker radii. No conversion to a global site-hit budget is
used when paying the first-order part at a single root. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset MeasureTheory Lattice RG Wilson Push Local Marker
open PhysicalNext.Repeat Lotus Merge Extra.Trajectories MergeProof MergeProof.Menu MergeProof.Accent
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {R : Rep G n} {I V : Type} [DecidableEq V]
variable {B : Census V} (t : I → Wing) (s : I → B.Mode) (F : I → Config G n → ℂ) (cap : I→ℝ)
variable (loc : ∀ i,UsesFinal R.p.threshold ((t i).support R) (F i))
variable (eligible : ∀ i U,F i U≠0 → (t i).qualifies R U) (blank : ∀ i,(t i).blank R)
variable (meas : ∀ i,Measurable (F i)) (gauge : ∀ i,GaugeInvariant (F i))
variable (bound : ∀ i U,‖F i U‖≤cap i) (hot : ∀ i,(s i).val.Nonempty)

include loc eligible blank meas gauge bound hot in
theorem rooted_hats [Fintype I] :
    ∃ q : I → Bool → Hat B R, (∀ i j,WKey (q i j)=t i ∧ (q i j).s=s i) ∧
      (∀ i U, ∑ j,amount (q i j) U = Poly.send (s i) (F i U)) ∧
      ∀ (w : V→ℝ) (y : V),
        (∑ i : I with y∈(s i).val, ∑ j : Bool,sumFee (q i j) w*load (q i j).M) =
        2*∑ i : I with y∈(s i).val, R.p.mass ((t i).support R) (Poly.toll w (s i)*cap i) := by
  choose q keys base value using fun i=> Menu.couple (R:=R) (t i) (s:=s i) (F i)
    (fun _ : V=>1) (loc i) (eligible i) (blank i) (meas i) (gauge i) (bound i) (hot i)
  refine ⟨q,keys,value,fun w y=>?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i _=>?_
  have price : (∑ j:Bool,‖(q i j).charge‖*(q i j).M.weight) = 2*cap i := by
    simpa only [Menu.fare,Menu.sumFee,Poly.toll,Finset.prod_const_one,one_mul] using base i
  have crest (j) : (q i j).M.crest = (t i).support R :=
    congrArg (fun k : Wing=>k.support R) (keys i j).1
  let a := Real.exp (R.p.supportExponent*coverNumber R.p.B ((t i).support R))
  change (∑ j : Bool,Poly.toll w (q i j).s*‖(q i j).charge‖*
    (Real.exp (R.p.supportExponent*coverNumber R.p.B (q i j).M.crest)*(q i j).M.weight)) =
      2*(a*(Poly.toll w (s i)*cap i))
  calc _ = ∑ j:Bool,(a*Poly.toll w (s i))*(‖(q i j).charge‖*(q i j).M.weight) := by
            apply sum_congr rfl
            intro j _
            rw [crest,(keys i j).2]
            dsimp only [a]
            ring
       _ = _ := by rw [←mul_sum,price]; ring

end YM.Integration.InletSusceptibility.JointShadow
