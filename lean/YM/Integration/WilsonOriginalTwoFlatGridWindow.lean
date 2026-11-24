import YM.Integration.WilsonOriginalTwoFlatGridCapture

/-! Uniformity in both dates of the coupling-power placement window. The
actual capture date may depend on the physical radius and the nodes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatGridWindow
open Function Filter Set Lattice RG Source Labels Wilson OPE Next.Rank Overlay Bid
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories RG16 RG16.Literal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Set Function Filter MeasureTheory
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale

include simple in
/-- Any selection in a polynomial window has the same spatial height as its
report. The proof also controls the one final block overshoot. -/
theorem height (k:ℕ)(s:ℕ→ℕ)(before:∀j,s j≤j)(window:∀j,a (s j)≤(β j)^k*a j):
    Height (C).S atTop σ s 1:=by
  have wage:=((height0 (hut C simple) (normal_height C)).power k).mul (normal_height C).mesh
  have h:RateIs atTop σ (fun j=>a (s j)) (-1):=by
    apply (normal_height C).mesh.of_sandwich ((wage.swap (by ring)).pays (C).S.divergent) _ _ (C).S.divergent
    · exact Eventually.of_forall fun j=>(C).S.strictAnti.antitone (before j)
    · exact Eventually.of_forall window
  refine ⟨tendsto_atTop.mpr fun n=>?_,?_⟩
  · filter_upwards [(h.tends (by norm_num) (C).S.divergent).eventually (gt_mem_nhds ((C).S.a_pos n))]
      with j hj using ((C).S.strictAnti.lt_iff_gt.mp hj).le
  · simpa only [Schedule.scale,Real.log_inv,neg_div,neg_neg] using! h.rate.neg

variable {I:Type}[Fintype I][DecidableEq I][Nonempty I](d:I→ℕ)
open WilsonOriginalTwoFlatGridCapture (word)

/-- The two quantities in the inequality are the unrestricted moment of the
literal physical product and the fixed flat reading of that same numerator. -/
def Heard (D j s u:ℕ) (ε:ℝ) : Prop :=
  ∀ok:u ≤ s,∀sj:s+1<j,∀N p:ℕ,∀hN:j<N,∀o:I → Cover,
    (∀i,8*‖(C).S.gridPoint j (o i)‖≤a (s+1)) →
    (Pairwise fun i i'=>2*a j*(((P).budget j).B:ℝ)^2 ≤
      ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀Y:∀i,(C).label (d i),(∀i,Spindle.paid C (d i) j N p (Y i)≤(β j)^D) →
    let F:=word R d j N p hN.le o Y
    ‖(C).omega N p F-WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (credit C N p 0 F s (by omega)) u ok‖≤ε

variable {r W pupil}(L:Package R.family W r pupil)
include L simple in
theorem original {J u:ℕ}(stop:Stop C 0 J u)(D k q:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀s:ℕ,s≤j → a s≤(β j)^k*a j → Heard R d D j s u ((β j)^q)⁻¹:=by
  let bad (j s:ℕ):Prop:=s≤j ∧ a s≤(β j)^k*a j ∧ ¬Heard R d D j s u ((β j)^q)⁻¹
  let pick (j:ℕ):=if h:∃s,bad j s then h.choose else j
  have take (j:ℕ)(h:∃s,bad j s):bad j (pick j):=by simpa only [pick,dif_pos h] using h.choose_spec
  have safe (j:ℕ):pick j≤j ∧ a (pick j)≤(β j)^k*a j:=by
    by_cases h:∃s,bad j s
    · exact ⟨(take j h).1,(take j h).2.1⟩
    · simp only [pick,dif_neg h,le_refl,true_and]
      exact le_mul_of_one_le_left ((C).S.a_pos j).le (one_le_pow₀ ((P).fits.delayed j).le)
  have cap:=height R simple k pick (fun j=>(safe j).1) (fun j=>(safe j).2)
  have cash:=height0 (hut C simple) (normal_height C)
  have rate : RateIs atTop σ (fun j=>(β j)^D) 0:=(cash.power D).swap (by ring)
  have available:=WilsonOriginalTwoFlatGridCapture.original R simple L d stop pick cap _ rate
  have finish:=((cash.power q).inv).overtakes
    ((RateIs.exp (-(1/32:ℝ)) (C).S.divergent).pays (C).S.divergent) (C).S.divergent (by norm_num)
  filter_upwards [available,finish] with j issued small
  intro s sj rent
  by_contra h
  obtain ⟨_,_,out⟩:=take j ⟨s,sj,rent,h⟩
  apply out
  intro ok sj N p hN o housing apart Y fee
  exact (issued ok sj N p hN o housing apart Y fee).trans small.le

end YM.Integration.WilsonOriginalTwoFlatGridWindow
end
