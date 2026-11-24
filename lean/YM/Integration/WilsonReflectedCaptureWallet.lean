import YM.Integration.WilsonReflectedThermometerCapture

/-! Before the period and cutoff, the collecting wage on the original
Wilson histories is paid along any launch and capture dates of height one.
The radius used at the initial slot is the genuine weak arm radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedCaptureWallet
open Function Filter Lattice Wilson RG Source OPE MergeProof Ribbons Accent
open ManyCopies Bid PhysicalNext.Repeat.Legato Bandage
open WilsonThermometerOwnOffsetRadii
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {J:Type*} {l:Filter J} {T:J→ℝ} {m k:J→ℕ}
local notation "C" => R.family
local notation "H" => R.family.path
local notation "δ" => renal R.alloy.B.a
local notation "φ" => near R.alloy.B.a
local notation "β" => R.alloy.B.a.clock.hatBeta

theorem slots (I:Type) [Fintype I] (t k:ℕ) :
    (∏ _i:I,δ k*radius R t k (k+1)/8)=
      (δ k*φ k/8)^(Fintype.card I)*((β k^t)⁻¹)^(Fintype.card I) :=by
  rw [radius_next R t k k le_rfl,radius_start]
  rw [Finset.prod_const,Finset.card_univ,←mul_pow]
  congr 1
  change _=(δ k*(β (k+1))⁻¹/8)*(β k^t)⁻¹
  ring

include simple book in
theorem original (I:Type) [Fintype I] [Nonempty I] (t h:ℕ)
    (time:Tendsto T l atTop) (cap:Height R.family.S l T m 1) (start:Height R.family.S l T k 1) :
    ∃ (α Z:J→ℝ), RateIs l T α 0 ∧ RateIs l T Z 0 ∧
      RateIs l T (fun j=>terminalCost R.family h (m j) (Z j)) (-(h:ℝ)) ∧
      ∀ j, 0 < α j ∧ α j ≤ 1 ∧
        (∀ i,i ≤ k j → α j ≤ license H δ (Fintype.card I) (carpet H i) (i+1)) ∧
        1 ≤ carpet H (m j) ∧ 0 < Z j ∧
        Z j=(α j)^(Fintype.card I)*compensation H (Fintype.card I) (m j+1) (k j) 0 (α j)
          (∏ _i:I,δ (k j)*radius R t (k j) (k j+1)/8) :=by
  let n:=Fintype.card I
  obtain ⟨y,rate,bounded,licensed⟩:=OPE.halls simple book.halos n Fintype.card_pos
  let α:=fun j=>y (k j)
  let rent:=fun j=>((β (k j)^t)⁻¹)^n
  let Z:=fun j=>initial H δ φ (m j) (k j) (α j) (rent j) n
  have cα:RateIs l T α 0:=height0 rate start
  have cr:RateIs l T rent 0:=(((height0 (hut R.family simple) start).power t).inv.power n).swap (by simp)
  have cZ:RateIs l T Z 0:=(Height.gathered cap start time cα cr simple n).swap (by ring)
  refine ⟨α,Z,cα,cZ,(key_cost cap time cZ simple h).swap (by ring),?_⟩
  intro j
  have eqn : Z j=(α j)^n*compensation H n (m j+1) (k j) 0 (α j)
      (∏ _i:I,δ (k j)*radius R t (k j) (k j+1)/8) :=by
    rw [slots]
    rfl
  have pos:0 < Z j:=by
    rw [eqn]
    apply mul_pos (pow_pos (rate.pos _) _)
    apply comp_pos (rate.pos _)
    apply Finset.prod_pos
    intro i _
    have δpos:=(mintN R.family simple).1.pos (k j)
    exact div_pos (mul_pos δpos (radius_pos R t _ _ (Nat.le_succ _))) (by norm_num)
  refine ⟨rate.pos _,bounded _,licensed _,?_,pos,eqn⟩
  change 0 < carpet H (m j)
  unfold carpet haloUnits
  positivity
end YM.Integration.WilsonReflectedCaptureWallet
