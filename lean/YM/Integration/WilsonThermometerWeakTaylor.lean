import YM.Integration.WilsonThermometerOwnOffsetWeakRows
import YM.Next.RANK.Carried
import YM.Trace.Physicalv2.GermPrices

/-! The genuine short and long regular occurrences of a charged thermometer
singleton on its weak detector. The short field polynomial is filed before
taking any Wick contractions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakTaylor
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open PhysicalNext.Repeat.Legato Trace.Physical GermGraph
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops Asymptotics
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d:ℕ} {n:Side} {F:Frame G d} {H:Hol G} {P:Rep G n}
variable (X:Coefficient F n) (m:ℕ)
abbrev Near := Subtype (fun j : ℕ => coverNumber P.p.B (X.support j) ≤ m)
abbrev Far := Subtype (fun j : ℕ => ¬coverNumber P.p.B (X.support j) ≤ m)

private theorem occurrences (form:X.Format 0 H P) {κ cash:ℝ} (paid:X.remBound 0 P κ cash) :
    Wrapper P.p (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) cash ∧
    Wrapper P.p (fun j:Far (P:=P) X m=>X.support j) (fun j=>X.regular j) (fun _=>1) (expCut P.p m*cash) := by
  obtain ⟨a,b,_,hb,total,_,⟨e,C,localBill⟩,_⟩ := paid
  have subtotal : a≤cash := (le_add_of_nonneg_right hb).trans total
  let M (j:ℕ) := P.p.mass (X.support j) (e j)
  have ez j := (localBill j).1
  have he : Summable e := C.2.1.of_nonneg_of_le ez (fun j=>P.p.loMass (X.support j) (e j) (ez j))
  have income : (∑' j,e j)≤cash := (he.tsum_le_tsum
    (fun j=>P.p.loMass (X.support j) (e j) (ez j)) C.2.1).trans (C.2.2.trans subtotal)
  let T := expCut P.p m
  have t0 : 0≤T := (Real.exp_pos _).le
  have remaining (j:Far (P:=P) X m) : e j.val ≤ T*M j.val := by
    change e _ ≤ Real.exp _ * (Real.exp _ * e _)
    rw [←mul_assoc,←Real.exp_add]
    apply le_mul_of_one_le_left (ez j.val) (Real.one_le_exp ?_)
    have hc := mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ) |>.mpr (Nat.lt_of_not_ge j.property).le)
      P.p.exponent_pos.le
    linarith only [hc]
  constructor
  · refine ⟨⟨fun j=>e j.val,fun j=>⟨form.smooth _,localBill _⟩,?_⟩,fun j=>form.origin _⟩
    simpa only [norm_one,one_mul] using (show SumBudget (fun j:Near (P:=P) X m=>e j.val) cash from
      ⟨fun j=>ez _,he.subtype _,(he.tsum_subtype_le e _ ez).trans income⟩)
  · have cost : (∑' j:Far (P:=P) X m,M j.val)≤cash :=
      (C.2.1.tsum_subtype_le M _ C.1).trans (C.2.2.trans subtotal)
    refine ⟨⟨fun j=>e j.val,fun j=>⟨form.smooth _,localBill _⟩,?_⟩,fun j=>form.origin _⟩
    simp only [norm_one,one_mul]
    refine ⟨fun j=>ez _,he.subtype _,?_⟩
    apply ((he.subtype _).tsum_le_tsum remaining ((C.2.1.subtype _).mul_left T)).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left cost t0

theorem original (S:Rules G) (D:ℕ) : ∃ c:ℝ,0≤c ∧
    ∀ {n:Side} {P:Rep G n} (X:Coefficient F n) (m b:ℕ)
      (_ : X.Format 0 H P) {κ cash:ℝ} (_ : X.remBound 0 P κ cash), D+1≤P.p.order →
    let rent := ((Fintype.card (links G (0:Site n) b):ℝ)+1)^D*c
    ∃ (u v:poly (links G (0:Site n) b)),
      Summary S P.p b D (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j)
        (fun _=>1) rent cash u ∧
      Summary S P.p b D (fun j:Far (P:=P) X m=>X.support j) (fun j=>X.regular j)
        (fun _=>1) rent (expCut P.p m*cash) v := by
  obtain ⟨c,c0,offers⟩ := bind S D
  refine ⟨c,c0,?_⟩
  intro n P X m b form κ cash paid order
  obtain ⟨close,distant⟩ := occurrences X m form paid
  obtain ⟨u,hu⟩ := offers _ _ _ b _ _ _ _ close order
  obtain ⟨v,hv⟩ := offers _ _ _ b _ _ _ _ distant order
  exact ⟨u,v,hu,hv⟩

theorem null_read (S:Rules G) {b D:ℕ} (closed : 10*b<n.val) (live : 2*(b+1)<n.val)
    (span : m*(4*P.p.B+2)+2*P.p.B≤b) (degree : d≤D) (form:X.Format 0 H P)
    {cash rent:ℝ} {u:poly (links G (0:Site n) b)}
    (row : Summary S P.p b D (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) rent cash u) (A:Snap G d) :
    evaluate_ray (walked (snips (o:=0) H live P.p A) u) d=0 := by
  obtain ⟨α,_,file⟩ := row
  obtain ⟨terms,listed,localRead⟩ := file.produced
  obtain ⟨_,_,_,rates⟩ := shades H A d D
  let pins := snips (o:=0) H live P.p A
  obtain ⟨W,observed⟩ := costs_ray d pins (rates _ _ _ live P.p).1
  have vanishes (j:Near (P:=P) X m) : W (terms j)=0 := by
    have contains : X.support j ⊆ Next.Rank.Spindle.patch b (0:Site n) := by
      intro e he
      rw [doors]
      exact (Corona.extent (X.support j) P.p.B (form.origin j.val) he).trans
        ((Nat.add_le_add_right (Nat.mul_le_mul_right _ j.property) _).trans span)
    have unwrap : Nonwrapping (X.support j) 0 := by
      intro x hx
      rw [separation_comm]
      exact (Nat.mul_le_mul_left 10 ((doors x).mp (contains hx))).trans_lt closed
    let body := fun h=>X.regular j (south H (0:Site n) A P.p.threshold h)
    obtain ⟨smooth,zeros⟩ := (form.projects j.val unwrap) (expand d (P.p.threshold • A))
    have exactJet := genuine H (X.support j) (X.regular j) P.p (1:ℂ) (terms j) S _
      (file.smooth j) contains live A (mul_nonneg (norm_nonneg _) (file.contact j).1) degree (localRead j).2
    change _ ∧ asym d ((fun h=>1*body h)-_) at exactJet
    simp only [one_mul] at exactJet
    rw [observed,←trill d smooth exactJet.1 exactJet.2]
    apply Finset.sum_eq_zero
    intro j hj
    change ((j.factorial:ℝ)⁻¹) • iteratedDeriv j body 0=0
    rw [show iteratedDeriv j body 0=0 from zeros j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),smul_zero]
  change evaluate_ray (walked pins u) d=0
  rw [←observed,←(value_at listed W).tsum_eq]
  simp only [vanishes,tsum_zero]

theorem head (R:Run G) (simple:G.Simple) (δ:ℝ) :
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N)
      (X:Coefficient (R.family.labels.level d) (R.family.side k p)) {cash:ℝ} (y:R.family.label d),
      reads d N p k X cash → Germ.projection (R.family.labels.level d) R.family.params
        (R.family.path.rep N p k).p.threshold 0 X=y →
      (R.family.labels.level d).coeffSize (y-X.x) ≤
        GermGraph.price (C:=R.family) d * Real.exp (δ*R.family.S.scale k) * cash := by
  filter_upwards [cut_flat R.family simple δ,eventually_ge_atTop (R.family.ref d)] with k cut ready
  intro N p hk X cash y paid germ
  have ht : (R.family.path.rep N p k).p=R.family.path.levels.budget k :=
    (R.makes.wilson.represents N p k hk).vac
  rw [ht] at germ
  have bound : (R.family.labels.level d).coeffSize (page (C:=R.family) d p k X-X.x) ≤
      GermGraph.invoice (C:=R.family) d k p * cash := measured_diff d N p k R.makes ready hk paid
  rw [show page d p k X=y from germ] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (cut p) (mul_nonneg (by positivity) (Germ.germ_close _ _).choose_spec.1.le))
    (rem_nonneg paid.2))

end YM.Integration.WilsonThermometerWeakTaylor
end
