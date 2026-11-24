import YM.Integration.WilsonCenteredFiledAtoms
import YM.Integration.WilsonReceivedSourceGross
import YM.Integration.WilsonRootedKioskCompleteFiling

/-! Plant one occupied group-word filing, with its original unmasked
value, at its named root in the chosen physical representation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedNominalRoot
open Finset Function Lattice Wilson RG Ac Source Labels Marker QuadraticLocal Push.AbsoluteSums
open Push.Local Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureLampRoster
open WilsonCenteredFiledAtoms WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V I T : Type} [DecidableEq V]
  {J : Census V} {o : V → Site n} {p : BudgetPoint} (L : Lamps T I G p o J)
  (s : J.Mode) (v : V) (hv : v∈s.val) (w : V→ℝ) (hw : ∀v,0<w v)

include hv hw in
private theorem loaded {a b : ℝ} (gross : Gross L w p.B a b) :
    ∃ f : Row L s→ℝ, (∀j,0≤f j) ∧ (∀ j t U,‖L.nominal t j.val U‖≤f j) ∧
      SumBudget (fun j:Row L s=>Real.exp (a*coverNumber p.B (L.ground j.val))*f j) ((Poly.toll w s)⁻¹*b) := by
  obtain ⟨f,pos,fee,account⟩:=gross.before
  let full (j:I):=if o v∈L.ground j then Poly.toll w (L.mode j)*f j*Real.exp (a*coverNumber p.B (L.ground j)) else 0
  have source : SumBudget full b:=account (o v)
  have sub : SumBudget (fun j:Row L s=>full j.val) b:=
    ⟨fun j=>source.1 _,source.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj source.2.1 source.1 Subtype.val_injective).trans source.2.2⟩
  refine ⟨fun j=>f j.val,fun j=>pos _,fun j=>fee j.val,?_⟩
  convert budget_scale (inv_pos.mpr (Poly.worth hw s)).le sub using 1
  funext j
  have root : o v∈L.ground j.val:=L.roots j.val v (by rw [j.property];exact hv)
  simp only [full,if_pos root,j.property]
  field_simp [(Poly.worth hw s).ne']

include hw in
private theorem reading {a b : ℝ} (apos : 0≤a) (gross : Gross L w p.B a b)
    (t:T) (U:Config G n) :
    HasSum (fun j:Row L s=>L.nominal t j.val U) ((bare L t U).part s) := by
  let f (j:I):=(Poly.send (L.mode j) (L.nominal t j U)).part s
  have ok:=(WilsonRootedKioskCompleteFiling.sums L hw apos gross t U).1
  have sums : HasSum f ((bare L t U).part s):=by
    rw [WilsonRootedKioskOccupiedSlip.bare,Poly.share ok];exact ((Poly.get s).hasSum ok.hasSum).summable.hasSum
  have off (j:I) (away:j∉Set.range ((↑):Row L s→I)) : f j=0:=by
    have miss : s≠L.mode j:=fun yes=>away ⟨⟨j,yes.symm⟩,rfl⟩
    simp [f,Poly.part_send,miss]
  apply ((Subtype.val_injective.hasSum_iff off).2 sums).congr_fun
  intro j
  simp [f,Poly.part_send,j.property]

include hv hw in
/-- The clear analytic component and its failed-mask exact correction are
entered as two parts of one original source, with all pre-existing hard
partners on the chosen Wilson history. -/
theorem mounted [Countable I] {d : ℕ} {F : Frame G d} (P : Rep G n)
    (same : P.p=p) (t:T) (S : SectionData F) (Y : Hol G)
    (keeper : Guard.Keeper P.p P.activities) {σ c Λ δ η κ μ E b : ℝ}
    (law : P.Lawful σ c Λ δ η) (read : Readable Y S P.p n μ)
    (hp : 0<κ) (hη : 0≤η) (room : hitWidth P.p*η≤1)
    (wage : L.Paid w p.B (p.supportExponent+2) E) (gross : Gross L w p.B (p.supportExponent+2) b) :
    Store P S Y (o v) κ (cartage P.p Y S μ η κ ((Poly.toll w s)⁻¹*E+(Poly.toll w s)⁻¹*b) 0)
      (fun U=>(P.eval U:ℂ)*(bare L t U).part s) := by
  subst p
  let α:=P.p.supportExponent+2
  have a0 : 0≤α:=by dsimp only [α];linarith only [P.p.exponent_pos]
  let site (j:Row L s):=L.ground j.val
  let f (j:Row L s):=L.nominal t j.val
  let h (j:Row L s):=f j-masked P.p.threshold (site j) (f j)
  obtain ⟨e,pos,caps,income⟩:=inlet L s v hv w hw wage
  obtain ⟨b',bp,grosscap,fees⟩:=loaded L s v hv w hw gross
  let a (j:Row L s):=e j+b' j
  have roots (j:Row L s):o v∈site j:=L.roots j.val v (by rw [j.property];exact hv)
  have adm : SumBudget (fun j=>reservedMass P.p (site j) (a j)) ((Poly.toll w s)⁻¹*E+(Poly.toll w s)⁻¹*b) := by
    convert sumBudget_add income fees using 1
    funext j;dsimp only [reservedMass,site,a];ring
  have caps' (j:Row L s) : P.p.supBounds (o v) (site j) (f j) (a j) := by
    have pay:=caps j t
    refine ⟨add_nonneg (pos _) (bp _),fun U ok l ds bound=>(pay.2 U ok l ds bound).trans ?_⟩
    exact le_add_of_nonneg_right (bp _)
  have attaches (j:Row L s) : Attaches P.p.threshold (site j) (h j) := by
    have g:=L.legal t j.val
    refine ⟨fun U W agree eqn=>congrArg₂ (·-·) (g.sites U W agree) (uses_mask _ g.sites U W agree eqn),
      fun k U=>congrArg₂ (·-·) (g.symmetry k U) (invariant_mask g.symmetry _ _ k U),
      g.borel.sub (masked_measurable _ _ _ g.borel),fun U ok=>sub_eq_zero.mpr (masked_eq _ _ _ _ ok).symm⟩
  have env (j:Row L s) (U:Config G n) : ‖h j U‖≤b' j := by
    by_cases ok:Healthy P.p.threshold (site j) U
    · simp only [h,Pi.sub_apply,masked_eq _ _ _ _ ok,sub_self,norm_zero];exact bp _
    · simpa only [h,Pi.sub_apply,masked_ne _ _ _ _ ok,sub_zero] using grosscap j t U
  have bs : Summable b':=fees.2.1.of_nonneg_of_le bp fun j=>le_mul_of_one_le_left (bp _)
    (Real.one_le_exp (mul_nonneg a0 (Nat.cast_nonneg _)))
  have ms (U:Config G n): Summable (fun j=>masked P.p.threshold (site j) (f j) U) := by
    apply Summable.of_norm_bounded bs
    intro j
    by_cases ok:Healthy P.p.threshold (site j) U
    · rw [masked_eq _ _ _ _ ok];exact grosscap j t U
    · rw [masked_ne _ _ _ _ ok,norm_zero];exact bp _
  have hs (U:Config G n): Summable (fun j=>h j U) := Summable.of_norm_bounded bs fun j=>env j U
  have blank : ForceFormat P.p P.activities (o v) 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have quiet : ForceCost P.p P.activities 0 (κ*0) := by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  obtain ⟨q,shape,charged,data,-⟩:=WilsonCenteredMountedCapture.original (o v) site
    (WilsonCenteredLampCapture.docket (Row L s)) keeper (WilsonCenteredLampCapture.docket (Row L s×Finset ℕ))
    0 f h 0 S Y law read hp hη room roots (fun j=>L.legal t j.val) a adm caps' attaches
    (fun j U=>(env j U).trans (le_add_of_nonneg_left (pos j))) blank quiet ms hs
  refine ⟨q,shape,charged.bound le_rfl,fun U=>?_⟩
  have unsummed (j:Row L s) : masked P.p.threshold (site j) (f j) U+h j U=f j U := by
    dsimp only [h,Pi.sub_apply];abel
  rw [data]
  simp_rw [unsummed]
  rw [(reading L s w hw a0 gross t U).tsum_eq]
  simp

end YM.Integration.WilsonReceivedNominalRoot
