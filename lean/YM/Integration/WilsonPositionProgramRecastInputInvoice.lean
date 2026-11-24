import YM.Integration.WilsonPositionProgramUniformGaussianCalendar
import YM.Integration.WilsonPositionProgramGaussianDriverExpense

/-! Restore the original radii once for every occupied generator and take the actual date's Gaussian height. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramRecastInputInvoice
open RG Lattice Tree Wilson PhysicalNext.Repeat.Legato Comparison.RG02
open Multi Marker Comparison.RG02.Order
open scoped Classical
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V} {r:ℕ}

def grade (p:Hot R→ℕ)(h:ℕ)(i:Hot (Board R r)):ℕ:=
  if u:(Join.left i.val).val.Nonempty then (p ⟨Join.left i.val,u⟩+(Join.right i.val).val.card)*h else 0

def fee (f:Hot R→ℕ→ℝ)(i:Hot (Board R r)):ℝ:=
  if u:(Join.left i.val).val.Nonempty then max 0 (f ⟨Join.left i.val,u⟩ (Join.right i.val).val.card) else 0

theorem positive (f:Hot R→ℕ→ℝ)(i:Hot (Board R r)):0≤fee f i:=by
  unfold fee
  split_ifs <;> positivity

theorem release {n w δ f c t A v x:ℝ}(hn:0<n)(hw:0<w)
    (sale:n*w*x ≤ f*(c*(δ*t*A))*v):x≤(δ/n)*(f*c*t*A/w)*v:=by
  calc
    x≤(f*(c*(δ*t*A))*v)/(n*w) := (le_div_iff₀ (mul_pos hn hw)).2 (by rwa [mul_comm x])
    _ = _ := by field_simp

def mean {G:Gauge}(R:Run G)(j:ℕ):ℝ:=Classical.choose (WilsonPositionProgramUniformGaussianCalendar.original R j)

theorem drawn {G:Gauge}(R:Run G)(N i per:ℕ)(live:i<N):
    let S:=R.family.path.levels.clock.op i per
    let F:=RegulatorIR.Halo.bios S
    let K:=(RunFormalChain.fromRun R).step N i per live
    ∀_tag:S.Choices,∀A:Exterior.fieldDir G (R.family.side i per) 1,∀z:(F.Free × G.ColorIndex)→ℝ,
      1+‖(Bulk.translated K F A z).2‖≤WilsonPositionProgramMeasuredFieldShift.height G
      (R.family.side i per) (mean R i) ‖A‖*(1+‖z‖):=by
  have h:=Classical.choose_spec (Classical.choose_spec (WilsonPositionProgramUniformGaussianCalendar.original R i))
  exact (h.2.2 N per live).2.2.1

end YM.Integration.WilsonPositionProgramRecastInputInvoice
end
