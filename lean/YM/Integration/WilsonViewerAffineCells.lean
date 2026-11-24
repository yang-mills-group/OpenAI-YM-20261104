import YM.Integration.WilsonViewerGridCells

/-! Pull the complete joint reporting test through its true affine coordinate map.
The cell keeps every physical-period alias of the original wrapped site. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerAffineCells
open Function Filter Set MeasureTheory Extraction Table Lattice Spec PhysicalNext.Repeat.Legato
open WilsonPositionPhysicalCellTest
open private visible from YM.Integration.WilsonPositionPhysicalCellTest
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{n:ℕ}

def anchor (r:ℝ)(s:ℕ)(o:Fin n → Cover):Points n:=
  WithLp.toLp 2 fun i=>r⁻¹ • R.family.S.gridPoint s (o i)

def pull (r:ℝ)(s:ℕ)(o:Fin n → Cover)(ξ:Points n):Points n:=
  anchor (R:=R) r s o+(R.family.S.a s/r) • ξ

theorem placement {r:ℝ}(rp:0<r)(s:ℕ)(o:Fin n → Cover)(ξ:Points n)(i:Fin n) :
    r • pull (R:=R) r s o ξ i=R.family.S.gridPoint s (o i)+R.family.S.a s • ξ i := by
  change r • (r⁻¹ • R.family.S.gridPoint s (o i)+(R.family.S.a s/r) • ξ i)=_
  rw [smul_add,smul_smul,smul_smul,mul_inv_cancel₀ rp.ne',one_smul]
  rw [show r*(R.family.S.a s/r)=R.family.S.a s by field_simp]

/-- Each child uses its own original digit before the common test is summed. -/
def child (s:ℕ)(o b:Fin n → Cover) : Fin n → Cover :=
  fun i a=>((R.family.S.block s).val:ℤ)*o i a+b i a

def tester (s:ℕ)(b:Fin n → Cover)(ξ:Points n):Points n:=
  ((R.family.S.block s).val:ℝ)⁻¹ • (WithLp.toLp 2 (fun i=>WithLp.toLp 2 (fun a=>(b i a:ℝ)))+ξ)

theorem child_pull {r:ℝ}(rp:0<r)(s:ℕ)(o b:Fin n → Cover)(ξ:Points n):
    pull (R:=R) r (s+1) (child (R:=R) s o b) ξ=pull (R:=R) r s o (tester (R:=R) s b ξ) := by
  ext i a
  change r⁻¹*(R.family.S.a (s+1)*(((R.family.S.block s).val:ℤ)*o i a+b i a : ℤ))+
      (R.family.S.a (s+1)/r)*ξ i a =
    r⁻¹*(R.family.S.a s*(o i a:ℝ))+(R.family.S.a s/r)*
      (((R.family.S.block s).val:ℝ)⁻¹*((b i a:ℝ)+ξ i a))
  have pos:0<((R.family.S.block s).val:ℝ):=by exact_mod_cast (R.family.S.block s).property
  rw [R.family.S.a_step]
  push_cast
  field_simp [rp.ne',pos.ne']
  ring

theorem mass_pull {r:ℝ}(rp:0<r)(s per:ℕ)(o:Fin n → Cover)(ψ:Test n)(u:Sites R (s,per) n) :
    mass (R:=R) ψ r (s,per) u =
      (R.family.S.a s/r)^(4*n) • ∫ξ:Points n,
        if site r (s,per) (pull (R:=R) r s o ξ)=u then ψ (pull (R:=R) r s o ξ) else 0 := by
  let C:=cell r (s,per) u
  let Y:=C.indicator (fun x=>ψ x)
  let b:=anchor (R:=R) r s o
  let h:=R.family.S.a s/r
  have hp:0<h:=div_pos (R.family.S.a_pos s) rp
  have mask(ξ:Points n): (if site r (s,per) (pull (R:=R) r s o ξ)=u
      then ψ (pull (R:=R) r s o ξ) else 0)=Y (b+h • ξ):=by
    by_cases live:site r (s,per) (pull (R:=R) r s o ξ)=u
    · have hit:b+h • ξ∈C:=live
      rw [if_pos live,show Y (b+h • ξ)=ψ (b+h • ξ) from Set.indicator_of_mem hit _]
      rfl
    · have miss:b+h • ξ∉C:=live
      rw [if_neg live,show Y (b+h • ξ)=0 from Set.indicator_of_notMem miss _]
  simp_rw [mask]
  change mass (R:=R) ψ r (s,per) u=h^(4*n) • ∫x:Points n,Y (b+h • x)
  have scale:=Measure.integral_comp_smul_of_nonneg volume (fun x:Points n=>Y (b+x)) h (hR:=hp.le)
  rw [Next.UVStress.point_dimension,integral_add_left_eq_self] at scale
  rw [scale,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hp.ne'),one_smul]
  exact (integral_indicator (f:=fun x=>ψ x) (μ:=volume) (visible (R:=R) r (s,per) u)).symm

theorem child_mass {r:ℝ}(rp:0<r)(s per:ℕ)(o b:Fin n → Cover)(ψ:Test n)(u:Sites R (s+1,per) n) :
    mass (R:=R) ψ r (s+1,per) u =
      (R.family.S.a (s+1)/r)^(4*n) • ∫ξ:Points n,
        if site r (s+1,per) (pull (R:=R) r s o (tester (R:=R) s b ξ))=u
        then ψ (pull (R:=R) r s o (tester (R:=R) s b ξ)) else 0 := by
  rw [mass_pull (R:=R) rp (s+1) per (child (R:=R) s o b) ψ u]
  simp_rw [child_pull (R:=R) rp]

end YM.Integration.WilsonViewerAffineCells
end
