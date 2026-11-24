import YM.Integration.WilsonOrdinaryNestedOutput
import YM.Integration.WilsonMacroscopicSharpPacket

/-! Sharp logarithmic upper price of the complete original ordinary moment at
one separated vertex, with its full state and fixed genuine exterior. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedWhole
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot GapsContact GapsContact.Seams GapsContact.Ascent
open Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z


include run in
theorem original {I T:Type} [Fintype I] [Fintype T] {d:I→ℕ} {e:T→ℕ}
    (v:Labels S d) (w:Labels S e) {M η δ:ℝ} (Mp:0≤M) (ηp:0<η) (δp:0<δ) :
    ∃ (K:ℝ) (l:ℕ), 0≤K ∧ ∀ᶠ r in trail,∀ x:I→E4,∀o:E4,∀y:T→E4,
      WithinRoom r M η x o → ClearOf o y δ → Injective (beside (sole o) y) →
      ∀u:Viewers F, ‖OPE.Orbits.whole (spectator F u) x v y w‖ ≤ K*badge r^l*r^(-weight d) := by
  obtain ⟨a,A,Ap,sharp⟩:=WilsonMacroscopicSharpPacket.on_ticket F Q run.facilities run.foundation
    run.original run.matrix 0 v w Mp ηp δp
  obtain ⟨b,B,Bp,head⟩:=WilsonMacroscopicLoggedRow.original F Q v run.facilities.toServices Mp ηp 0
    (WilsonMacroscopicLoggedRow.issued F Q v run.sharp Mp ηp 0)
  obtain ⟨D,Dp,finish⟩:=WilsonMacroscopicViewerCharge.uniform F run.facilities.toServices 0 w δp
  let U: S.Field 0→L[ℂ]S.Field 0 := (F.sector.derivatives.rise (d:=0) (le_refl 0)).toContinuousLinearMap
  refine ⟨A+D*‖U‖*B,a+b,by positivity,?_⟩
  filter_upwards [head,sharp,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with r hh hs rp r1 x o y room clear one u
  have hr:0<r:=rp
  have rsmall:r≤1:=r1
  have badge1:1≤badge r:=by unfold badge OPE.run;linarith [Real.log_nonpos hr.le rsmall]
  have pows (j:ℕ) (hj:j≤a+b):badge r^j≤badge r^(a+b):=pow_le_pow_right₀ badge1 hj
  have price:=hh x o room
  rw [Nat.cast_zero,zero_sub] at price
  have ret:=((hs x o y room clear).2 u)
  rw [Nat.cast_zero,zero_add,show (1:ℝ)-weight d = 1 + (-weight d) from sub_eq_add_neg ..,Real.rpow_add hr,Real.rpow_one] at ret
  have packed : Q.packet 0 x v o = U (Q.fresh 0 x o v):=by
    unfold Reader.packet
    letI : Subsingleton (Fin (0+1)) := ⟨fun a b=>Fin.ext (by omega)⟩
    rw [Fintype.sum_subsingleton _ (0 : Fin (0+1))]
    rfl
  have hsmall : r*r^(-weight d)≤r^(-weight d):=mul_le_of_le_one_left
    (Real.rpow_nonneg hr.le _) rsmall
  have h1: A*badge r^a*(r*r^(-weight d))≤A*badge r^(a+b)*r^(-weight d):=by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pows _ (Nat.le_add_right ..)) Ap.le) hsmall
      (mul_nonneg hr.le (Real.rpow_nonneg hr.le _)) (mul_nonneg Ap.le (pow_nonneg (zero_le_one.trans badge1) _))
  have full:=finish o y clear one u (Q.packet 0 x v o)
  rw [packed] at full
  calc
    _ ≤ ‖OPE.Orbits.whole (spectator F u) x v y w-upon (spectator F u) 0 o y w (Q.packet 0 x v o)‖+
      ‖upon (spectator F u) 0 o y w (Q.packet 0 x v o)‖:=by
        generalize (OPE.Orbits.whole (spectator F u) x v y w)=X
        generalize (upon (spectator F u) 0 o y w (Q.packet 0 x v o))=Y
        simpa only [sub_add_cancel] using norm_add_le (X-Y) Y
    _ ≤ A*badge r^(a+b)*r^(-weight d) + D*‖U‖*(B*badge r^(a+b)*r^(-weight d)):=by
      apply add_le_add (ret.trans h1)
      rw [packed]
      refine full.trans ?_
      calc
        _ ≤ D*(‖U‖*(B*badge r^b*r^(-weight d))):=mul_le_mul_of_nonneg_left
          ((U.le_opNorm _).trans (mul_le_mul_of_nonneg_left price (norm_nonneg U))) Dp
        _ ≤ D*(‖U‖*(B*badge r^(a+b)*r^(-weight d))):=by gcongr; omega
        _ = _:=by ring
    _ = _:=by ring
end YM.Integration.WilsonOrdinaryNestedWhole
