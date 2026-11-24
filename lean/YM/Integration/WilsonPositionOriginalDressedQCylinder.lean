import YM.Integration.WilsonPositionOriginalDiagnosticHalfSpace
import YM.Push.GRID_APPROXIMATION.Iterate
import YM.OPE.Therm.Request

/-! Space burned by transporting an actual unmarked or Q test to the microscopic
reflection plane. The statement is uniform in both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQCylinder
open Finset Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox WilsonPositionOriginalDiagnosticHalfSpace
open RG16 RG16.Literal
open private paid from YM.Integration.WilsonPositionOriginalDiagnosticHalfSpace
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "Λ" => RG16.Lambda R.family.path.levels

def stencil (h:ℕ):ℕ:=1+∑a:Axis,radius R h a

theorem footprint {h d:ℕ}(hd:d≤h)(date per:ℕ)(o:Site (R.family.side date per)):
    ↑((R.family.localSection d).footprint o) ⊆ window o (stencil R h):=by
  rintro z hz
  change z∈(R.family.localSection d).stencil.image _ at hz
  obtain ⟨v,hv,rfl⟩:=mem_image.mp hz
  refine ⟨v,?_,rfl⟩
  have cover(a:Axis):(v a).natAbs≤ stencil R h:= by
    have b:=paid R a hd hv
    have s:=single_le_sum (s:=(univ:Finset Axis)) (f:=fun j=>radius R h j)
      (fun j _=>Nat.zero_le _) (mem_univ a)
    unfold stencil;omega
  change v∈Finset.Icc _ _
  exact Finset.mem_Icc.mpr ⟨fun a=>by have:=cover a;change -(stencil R h:ℤ)≤v a;omega,
    fun a=>by have:=cover a;change v a≤(stencil R h:ℤ);omega⟩

/-- An arbitrary signed field supported in this microscopic window can enter
the same reflection form as its genuinely dressed partner. -/
theorem sheet_window (N per w:ℕ)(a:Axis)(o:Site (R.family.side N per))
    (low:0<w)(high:3*w<(Cells.half R.family.S N per).val):
    window o w ⊆ (sheet R N per a o (2*w)).sector:=by
  rintro z ⟨v,hv,rfl⟩
  change v∈Finset.Icc _ _ at hv
  have lo':= (Finset.mem_Icc.mp hv).1 a
  have hi':= (Finset.mem_Icc.mp hv).2 a
  change -(w:ℤ)≤v a at lo';change v a≤(w:ℤ) at hi'
  let n:=R.family.side N per
  let J:ℤ:=((2*w:ℕ):ℤ)+v a
  have lo:0<J:=by dsimp only [J];omega
  have hi:J<(Cells.half R.family.S N per).val:=by dsimp only [J];omega
  have side:=Cells.original R.family.S N per
  have jn:J.toNat<n.val:=by change J.toNat<(R.family.S.side N per).val;omega
  have shift: ((wrap n v a+o a)-(o a-((2*w:ℕ):Per n)):Per n)=(J.toNat:Per n):=by
    have eq':(J.toNat:ℤ)=J:=Int.toNat_of_nonneg lo.le
    have eq:=congrArg (fun t:ℤ=>(t:Per n)) eq'
    change ((v a:ℤ):Per n)+o a-(o a-((2*w:ℕ):Per n))=_
    calc
      _ = ((J:ℤ):Per n):=by dsimp only [J];push_cast;ring
      _ = _:=by simpa only [Int.cast_natCast] using eq.symm
  change 0<(((wrap n v a+o a)-(o a-((2*w:ℕ):Per n)):Per n)).val ∧
    (((wrap n v a+o a)-(o a-((2*w:ℕ):Per n)):Per n)).val<(Cells.half R.family.S N per).val
  rw [shift,ZMod.val_natCast_of_lt jn];omega

theorem current (Y:OPE.Therm.Poetry R.family.path.levels)(simple:G.Simple)(h:ℕ):
    ∀ᶠ m:ℕ in atTop,4*(R.family.S.a m*stencil R h+tail R.family.path.levels m)≤R.family.S.a m*(Λ m)^2:=by
  filter_upwards [(lambda_leads R.family simple).eventually_ge_atTop (484:ℝ),
    (lambda_leads R.family simple).eventually_ge_atTop (4*(stencil R h:ℝ))] with m large price
  have hj:((R.family.path.levels.clock.J m):ℝ)+5 ≤ 4*(Λ m):=by
    have hh:=(Y.stage m).pedestal
    have h':=lambda_up R.family m
    have hc:=Nat.cast_nonneg (α:=ℝ) (R.family.path.levels.clock.J m)
    unfold RG16.Lambda at h' ⊢;linarith
  have bill:4*((stencil R h:ℝ)+30*((R.family.path.levels.clock.J m:ℝ)+5))≤(Λ m)^2:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr large) (show 0≤Λ m by linarith)]
  calc
    _ =R.family.S.a m*(4*((stencil R h:ℝ)+30*((R.family.path.levels.clock.J m:ℝ)+5))):=by unfold tail;ring
    _ ≤ _:=mul_le_mul_of_nonneg_left bill (R.family.S.a_pos _).le

end YM.Integration.WilsonPositionOriginalDressedQCylinder
