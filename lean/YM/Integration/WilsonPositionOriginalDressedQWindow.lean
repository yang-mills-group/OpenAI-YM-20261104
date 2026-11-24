import YM.Integration.WilsonPositionOriginalDressedQCylinder

/-! A physical separation and a genuine offset collar chosen before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQWindow
open Filter Set Function MeasureTheory Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox
open WilsonPositionOriginalDiagnosticHalfSpace WilsonPositionOriginalDressedQCylinder
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "Λ" => RG16.Lambda R.family.path.levels

private theorem integral_width (N:ℕ)(r:ℝ)(b:ℕ)(paid:4*R.family.S.a N*b≤r):
    b≤width R r N:=by
  apply Nat.le_floor
  have pos:0<((R.family.S.denominator N).val:ℝ):=by exact_mod_cast (R.family.S.denominator N).property
  have rate:((R.family.S.denominator N).val:ℝ)*R.family.S.a N=1:=by simp [Schedule.a,pos.ne']
  have fine:=mul_le_mul_of_nonneg_left paid pos.le
  calc
    (b:ℝ) = ((R.family.S.denominator N).val:ℝ)*(4*R.family.S.a N*b)/4:=by
      linear_combination -b*rate
    _ ≤ r*((R.family.S.denominator N).val:ℝ)/4:= by linarith

theorem charged (Y:OPE.Therm.Poetry R.family.path.levels)(simple:G.Simple)(h:ℕ):
    ∀ᶠ m : ℕ in atTop, ∀ r : ℝ, 0 < r → r ≤ 1 → 2*R.family.S.a m*(Λ m)^2 ≤ r →
      ∀ w : ℕ, 8*R.family.S.a m*w ≤ r → ∀ N per, ∀ live : m ≤ N, ∀ a : Axis, ∀ o : Site (R.family.side N per),
      window o (grows R.family.path.levels m (w+stencil R h) live) ⊆
        (sheet R N per a o (2*width R r N)).sector:=by
  filter_upwards [current R Y simple h] with m spent
  intro r positive small scale w offset N per live a o
  have native:=scales_budget R.family.path.levels m (w+stencil R h) live
  have tail_nonneg:0≤tail R.family.path.levels N:=(tail_pos ..).le
  have cost:4*R.family.S.a N*(grows R.family.path.levels m (w+stencil R h) live)≤r:=by
    push_cast at native
    linarith only [native,spent,offset,scale,tail_nonneg]
  have count:=integral_width R N r _ cost
  have enough:4*R.family.S.a N*(1:ℕ)≤r:=by
    have c:1≤ stencil R h:=by unfold stencil;omega
    have cd:=mul_le_mul_of_nonneg_left (show (1:ℝ)≤ stencil R h by exact_mod_cast c) (R.family.S.a_pos m).le
    have old:=R.family.S.strictAnti.antitone live
    have seed:0≤tail R.family.path.levels m:=(tail_pos ..).le
    have oprice:0≤R.family.S.a m*w:=mul_nonneg (R.family.S.a_pos m).le (Nat.cast_nonneg _)
    push_cast;linarith only [spent,offset,scale,cd,old,seed,oprice]
  have lower:=integral_width R N r 1 enough
  have den:= (R.family.S.denominator N).property
  have dh: (R.family.S.denominator N).val≤(Cells.half R.family.S N per).val:=by
    have base:=Cells.original R.family.S N per
    change (R.family.S.period per).val*(R.family.S.denominator N).val=2*(Cells.half R.family.S N per).val at base
    have four:=R.family.S.period_four per
    have q:2≤(R.family.S.period per).val:=(by decide:2≤4).trans (Nat.le_of_dvd (R.family.S.period per).property four)
    have hh:=Nat.mul_le_mul_right (R.family.S.denominator N).val q
    omega
  have upper:4*width R r N≤(R.family.S.denominator N).val:=by
    have floor:=Nat.floor_le (show 0≤r*((R.family.S.denominator N).val:ℝ)/4 by positivity)
    have hd:=mul_le_mul_of_nonneg_right small (Nat.cast_nonneg (α:=ℝ) (R.family.S.denominator N).val)
    change 4*⌊r*((R.family.S.denominator N).val:ℝ)/4⌋₊≤_
    exact_mod_cast (show (4:ℝ)*(⌊r*((R.family.S.denominator N).val:ℝ)/4⌋₊:ℝ)≤(R.family.S.denominator N).val by linarith)
  apply Set.Subset.trans _ (sheet_window R N per (width R r N) a o (by omega) (by omega))
  rintro z ⟨u,hu,rfl⟩
  exact ⟨u,box_larger hu count,rfl⟩

end YM.Integration.WilsonPositionOriginalDressedQWindow
