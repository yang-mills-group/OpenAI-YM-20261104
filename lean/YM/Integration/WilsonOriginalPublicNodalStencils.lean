import YM.Integration.WilsonOriginalPublicNodalCanonical

/-! Each paid public column as its original curvature stencil on every
auxiliary side, with the native Laurent price transported from the measured clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalStencils
open Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open ActualRunPhysicalPages ActualRunCurvaturePackets
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonOriginalStarSceneWords (pole raw)
open WilsonReceivedCanonicalVerseBasis (dose restored)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}(d:I→ℕ)(a:Columns R d)
variable {N p K:ℕ}(live:K≤N){h:I→ℕ}(κ:(j:I)→Knob (h j))(pt:I→Chamber)
local notation "g" => regulatorRun R.family N p K
local notation "τ" => (R.family.path.rep N p K).p.threshold
local notation "F" j:max => R.family.labels.level (d j)
local notation "v" => request R d a (N:=N) (p:=p) (K:=K)
local notation "socket" j:max => WilsonOriginalStarLaurentWallet.Socket R (d j)
local notation "co" j:max c:max => dose R d N p K v j c

include live in
private theorem softened (j:I)(c:socket j):
    (g:ℂ)^(-(WilsonOriginalStarLaurentWallet.lag R (d j) c:ℤ))*co j (.inr c)=
      ((F j).core (Pi.single (a j) 1)) c.1*WilsonOriginalStarLaurentWallet.shape R (d j) c:=by
  classical
  have gp:=ActualRunKernelPackets.regulator_pos R N p K live
  have tp:0<τ:=(R.family.path.rep N p K).p.threshold_pos
  rw [show co j (.inr c)=WilsonOriginalStarLaurentWallet.coefficient R (d j) g τ ((F j).core (v j)) c by rfl,
      WilsonOriginalStarLaurentWallet.normalized R (d j) g τ gp]
  let n:=WilsonOriginalStarLaurentWallet.lag R (d j) c
  have scaled:((F j).core (v j)) c.1=(τ:ℂ)^n*((F j).core (Pi.single (a j) 1)) c.1:=by
    by_cases z:c.1=0
    · simp [Labels.Frame.core,Function.update,z]
    · change Function.update ((F j).scaled τ (Pi.single (a j) 1)) 0 0 c.1=
        (τ:ℂ)^n*Function.update (Pi.single (a j) 1:(F j).Coeff) 0 0 c.1
      rw [Function.update_of_ne z,Function.update_of_ne z,Labels.Frame.scaled_apply,Complex.ofReal_pow]
      rfl
  rw [scaled,Complex.ofReal_pow,Complex.ofReal_inv,inv_pow]
  have nz:(τ:ℂ)^n≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr tp.ne')
  change (((τ:ℂ)^n)⁻¹*((τ:ℂ)^n*_))*_=_
  rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]

private theorem native (j:I)(w:(F j).Index){n:Side}(o:Site n)(U:Config G n):
    ∑m:↥((ofRun R (d j)).data.shape w).support,WilsonOriginalStarLaurentWallet.shape R (d j) ⟨w,m⟩*
      (((raw R d (entry R d j (.inr ⟨w,m⟩))).unmasked U o:ℝ):ℂ)=
    (R.family.localSection (d j)).places (Pi.single w 1) o U:=by
  rw [placed_basis (ofRun R (d j)) w o U]
  let A:=ofRun R (d j)
  let f (m:(Fin (A.data.count w)×G.ColorIndex)→₀ℕ):ℂ:=MvPolynomial.coeff m (A.data.shape w)*
    NativeCurvatureTensor.value (fun k=>(NativeCurvatureTensor.word m k).2)
      (fun k=>(A.data.columns w (NativeCurvatureTensor.word m k).1).atSite U o)
  calc _=∑m:↥(A.data.shape w).support,f m.val:=by
         apply sum_congr rfl
         intro m _
         change _*(((WilsonOriginalProjectedCurvatureAtom.atom _ _).unmasked U o:ℝ):ℂ)=_
         rw [WilsonOriginalProjectedCurvatureAtom.unmasked]
         rfl
       _= _:=Finset.sum_coe_sort (A.data.shape w).support f

include live in
theorem letter (j:I){n:Side}(o:Site n)(U:Config G n):
    (R.family.localSection (d j)).places (Pi.single (a j) 1) o U=
      ∑c:Choice R d j,co j c*restored R d κ pt g j c o U:=by
  classical
  have scalar:co j (.inl ())*restored R d κ pt g j (.inl ()) o U=(Pi.single (a j) 1:(F j).Coeff) 0:=by
    rw [restored,WilsonReceivedCanonicalVerseBasis.field]
    change (F j).scaled τ (Pi.single (a j) 1) 0*((g:ℂ)^(-(0:ℤ))*
      (((raw R d (.inl j)).unmasked U o:ℝ):ℂ))=_
    simp [Labels.Frame.scaled_apply,(F j).zero_degree,raw,WilsonOriginalStarSceneWords.rank,
      Atom.unmasked,Atom.poly]
  have combined(c:socket j):
      co j (.inr c)*restored R d κ pt g j (.inr c) o U=
        (((F j).core (Pi.single (a j) 1)) c.1*WilsonOriginalStarLaurentWallet.shape R (d j) c)*
          (((raw R d (entry R d j (.inr c))).unmasked U o:ℝ):ℂ):=by
    rw [restored,WilsonReceivedCanonicalVerseBasis.field,←mul_assoc,mul_comm (co j (.inr c))]
    rw [show pole R d (entry R d j (.inr c))=WilsonOriginalStarLaurentWallet.lag R (d j) c by rfl,softened R d a live j c]
  rw [Fintype.sum_sum_type,Fintype.sum_unique,show (default:Unit)=() by rfl,scalar]
  simp_rw [combined]
  rw [Fintype.sum_sigma]
  simp_rw [mul_assoc,←Finset.mul_sum,native R d]
  by_cases zero:a j=0
  · rw [zero]
    have z:(F j).core (Pi.single (0:(F j).Index) 1)=0:=by
      ext w
      by_cases eqn:w=0
      · subst w;rfl
      · change Function.update (Pi.single 0 1:(F j).Coeff) 0 0 w=0
        rw [Function.update_of_ne eqn,Pi.single_eq_of_ne eqn]
    rw [z]
    simp
    exact congrFun (R.makes.sections (d j)).unit _
  · have unchanged:(F j).core (Pi.single (a j) 1)=Pi.single (a j) 1:=by
      ext w
      by_cases eqn:w=0
      · subst w;change 0=(Pi.single (a j) 1:(F j).Coeff) 0
        rw [Pi.single_eq_of_ne (Ne.symm zero)]
      · exact Function.update_of_ne eqn ..
    rw [unchanged,Pi.single_eq_of_ne (Ne.symm zero),zero_add]
    simp [Pi.single_apply]

/-- The marked Laurent factor is restored once at the changed coupling. -/
def retime (t:ℝ)(j:I)(c:Choice R d j):ℂ:=
  (t:ℂ)^(pole R d (entry R d j c))*(g:ℂ)^(-(pole R d (entry R d j c):ℤ))

include live in
theorem priced (t:ℝ)(ht:t≠0)(j:I){n:Side}(o:Site n)(U:Config G n):
    (R.family.localSection (d j)).places (Pi.single (a j) 1) o U=
      ∑c:Choice R d j,(co j c*retime R d (N:=N) (p:=p) (K:=K) t j c)*
        restored R d κ pt t j c o U:=by
  rw [letter R d a live κ pt j o U]
  apply sum_congr rfl
  intro c _
  let k:=pole R d (entry R d j c)
  have nz:(t:ℂ)^k≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht)
  unfold retime restored
  simp only [zpow_neg,zpow_natCast]
  change _=(_*((t:ℂ)^k*_))*(((t:ℂ)^k)⁻¹*_)
  field_simp

end YM.Integration.WilsonOriginalPublicNodalStencils
end
