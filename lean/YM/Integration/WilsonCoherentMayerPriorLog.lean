import YM.Integration.WilsonCoherentMayerPriorCapacity

/-! Connected reading of an actual measured partition and a separately submitted full marked numerator. Both use their own quiet coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorLog
open Function Finset Marker Multi Comparison.RG02.Cumulants Extra.Trajectories
open WilsonCoherentMayerPriorCapacity
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V][Fintype V]{Γ:Census V}

def normalized (x:Poly Γ):Poly Γ:=(x.part Γ.quiet)⁻¹ • x

def bill (Γ:Census V)(a:ℝ):ℝ:=2*(1+a)*count Γ*(1+2*a)^degree Γ

theorem paid (x y:Poly Γ)(quiet:x.part Γ.quiet=1){δ a:ℝ}(dp:0≤δ)(half:δ≤1/2)
    (ap:0≤a)(bounded:∀s,‖x.part s‖≤a)(agrees:∀s,‖x.part s-y.part s‖≤δ):
    y.part Γ.quiet≠0 ∧ ∀s:Γ.Mode,
      ‖(connected x-connected (normalized y)).part s‖≤δ*bill Γ a:=by
  let b:=y.part Γ.quiet
  have close:‖(1:ℂ)-b‖≤δ:=by simpa only [b,quiet] using agrees Γ.quiet
  have triangle:1≤‖(1:ℂ)-b‖+‖b‖:=by simpa using norm_add_le ((1:ℂ)-b) b
  have low:1/2≤‖b‖:=by linarith
  have nz:b≠0:=norm_pos_iff.mp (by linarith)
  have inv:‖b⁻¹‖≤2:=by rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr nz)];linarith
  have unit:(normalized y).part Γ.quiet=1:=inv_mul_cancel₀ nz
  let E:=2*δ*(1+a)
  have ep:0≤E:=by dsimp [E];positivity
  have estimate (s:Γ.Mode):‖x.part s-(normalized y).part s‖≤E:=by
    rw [norm_sub_rev];change ‖b⁻¹*y.part s-x.part s‖≤_
    have id:b⁻¹*y.part s-x.part s=b⁻¹*((y.part s-x.part s)+(1-b)*x.part s):=by field_simp;ring
    rw [id,norm_mul]
    have increment:‖y.part s-x.part s‖≤δ:=by rw [norm_sub_rev];exact agrees s
    have terms:=norm_add_le (y.part s-x.part s) ((1-b)*x.part s)
    rw [norm_mul] at terms
    have h:=terms.trans (add_le_add increment (mul_le_mul close (bounded s) (norm_nonneg _) dp))
    calc _≤2*(δ+δ*a):=mul_le_mul inv h (norm_nonneg _) (by norm_num)
         _=E:=by dsimp [E];ring
  refine ⟨nz,fun s=>?_⟩
  have prev:=WilsonCoherentMayerPriorPartitions.original x (normalized y) quiet unit ep estimate s
  have e1:E≤1+a:=by dsimp [E];nlinarith only [half,mul_nonneg (sub_nonneg.mpr half) ap]
  have prices:=finite Γ x ep (a:=1+2*a) (by linarith) (fun i=>by linarith only [bounded i,e1]) s
  calc _≤E*(count Γ*(1+2*a)^degree Γ):=prev.trans (mul_le_mul_of_nonneg_left prices ep)
       _=δ*bill Γ a:=by dsimp only [E,bill];ring

/-- The filed log splits off exactly the separately submitted polynomial while retaining all prior signed submoments. -/
theorem filed (q old:Poly Γ)(unmarked:q.part Γ.quiet=0)(present:old.part Γ.quiet≠0):
    connected (normalized (Poly.pass q*old))=q+connected (normalized old):=by
  have t:(Poly.pass q).part Γ.quiet=1:=Poly.pass_part _ unmarked
  have h:normalized (Poly.pass q*old)=Poly.pass q*normalized old:=by
    unfold normalized;rw [Poly.quiet_mul,t,one_mul,mul_smul_comm]
  have drawn:(normalized old).part Γ.quiet=1:=inv_mul_cancel₀ present
  rw [h,connected_mul t drawn,connected_pass unmarked]

end YM.Integration.WilsonCoherentMayerPriorLog
