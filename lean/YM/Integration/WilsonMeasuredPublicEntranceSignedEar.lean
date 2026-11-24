import YM.Integration.WilsonMeasuredPublicEntranceFlatShares
import YM.Integration.WilsonMeasuredPublicEntranceGridCompensation
/-! Signed recomposition at the lower Wilson law. The conditional acts on
the entire finite difference, with the original positive vacuum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSignedEar
open Function Finset MeasureTheory Lattice RG Wilson Marker Poly OPE.Therm
open PhysicalNext PhysicalNext.Repeat Legato WilsonThermometerUnitFilingCoarse WilsonOriginalAlternativeHearing
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}{N p f:ℕ}
local notation "cfg" => Config G (R.family.side f p)
local notation "P" => R.family.path.rep N p f

def weighted (F:cfg → ℂ)(U:cfg):ℂ:=((P).eval U:ℂ)*F U

def cheap (x e:V → cfg → ℂ)(vs:List V)(U:cfg):ℂ:=route (fun i=>x i U) (fun i=>x i U-e i U) (fun i=>e i U) vs

theorem minus {F K:cfg → ℂ}(hf:BoundedAt R.family F)(hk:BoundedAt R.family K):
    BoundedAt R.family (fun U=>F U-K U):=by
  obtain ⟨m,M,hm⟩:=hf
  obtain ⟨b,B,hb⟩:=hk
  exact ⟨m.sub b,M+B,fun U=>(norm_sub_le ..).trans (add_le_add (hm U) (hb U))⟩

theorem regular (x e:V → cfg → ℂ)(vs:List V)
    (h:∀i,BoundedAt R.family (x i))(he:∀i,BoundedAt R.family (e i)):
    BoundedAt R.family (cheap R x e vs):=by
  have c(U:cfg):cheap R x e vs U=factors x vs U-factors (fun i U=>x i U-e i U) vs U:=by
    have charge:=crossed (1:ℂ) (fun i=>x i U) (fun i=>x i U-e i U) (fun i=>e i U) (by intro i;ring) vs
    simpa only [cheap,factors,one_mul] using charge.symm
  rw [funext c]
  exact minus R (collection R.family x h vs) (collection R.family _ (fun i=>minus R (h i) (he i)) vs)

theorem weighted_integrable (live:f ≤ N){F:cfg → ℂ}(h:BoundedAt R.family F):
    Integrable (weighted (N:=N) R F) (prior G _):=by
  change Integrable (fun U=>((P).eval U:ℂ)*F U) (prior G _)
  simpa only [Complex.real_smul] using integrable R.family R.makes live h

theorem numerical (live:f ≤ N){b:ℕ}(lo:b ≤ f)(x e:V → cfg → ℂ)(n δ:V → ℝ)(vs:List V)
    (px:∀i U,‖x i U‖ ≤ n i)(pe:∀i U,‖e i U‖ ≤ δ i):
    ‖reading R (N:=N) (weighted (N:=N) R (cheap R x e vs)) b lo‖ ≤ route n (fun i=>n i+δ i) δ vs:=by
  have received:=normalized R.family N p R.makes live (weighted (N:=N) R (cheap R x e vs)) lo
  have hear:reading R (N:=N) (weighted (N:=N) R (cheap R x e vs)) b lo=
      held R.family N p (weighted (N:=N) R (cheap R x e vs)) lo (1:Config G (R.family.side b p)):=by
    simp only [reading,held,Complex.real_smul,Complex.ofReal_inv]
  rw [hear,received]
  apply actualTransport_norm_le R.family R.makes live _ lo
  intro U
  have nz:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  simp only [weighted,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  exact price _ _ _ _ (fun i=>px i U) (fun i=>pe i U) vs


theorem original (live:f ≤ N){b:ℕ}(lo:b ≤ f)(s:Finset V)(x y e ax ay az:V → cfg → ℂ)
    (hx:∀i,BoundedAt R.family (x i))(hy:∀i,BoundedAt R.family (y i))(he:∀i,BoundedAt R.family (e i))
    (sheet:∀i U,((P).eval U:ℂ)*(y i U-(x i U-e i U))=ax i U-ay i U-az i U)
    (n δ:V → ℝ)(px:∀i U,‖x i U‖ ≤ n i)(pe:∀i U,‖e i U‖ ≤ δ i)
    (T:ℝ)(int:Integrable (WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az) (prior G _))
    (received:‖reading R (N:=N) (WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az) b lo‖ ≤ T):
    let lifted:=fun F=>reading R (N:=N) (weighted (N:=N) R F) b lo
    let h:=WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az
    lifted (factors x s.toList)-lifted (factors y s.toList)=lifted (cheap R x e s.toList)-reading R (N:=N) h b lo ∧
    ‖lifted (factors x s.toList)-lifted (factors y s.toList)‖ ≤ route n (fun i=>n i+δ i) δ s.toList+T:=by
  intro ear h
  have left:=weighted_integrable R live (collection R.family x hx s.toList)
  have right:=weighted_integrable R live (collection R.family y hy s.toList)
  have c:=weighted_integrable R live (regular R x e s.toList hx he)
  have field:(fun U=>weighted (N:=N) R (factors x s.toList) U-weighted (N:=N) R (factors y s.toList) U)=
      (fun U=>weighted (N:=N) R (cheap R x e s.toList) U-h U):=by
    funext U
    simp only [weighted,←mul_sub]
    exact WilsonMeasuredPublicEntranceCheapOrder.original _ _ _ _ _ (fun i=>sheet i U) s.toList
  have equality:ear (factors x s.toList)-ear (factors y s.toList)=ear (cheap R x e s.toList)-reading R (N:=N) h b lo:=by
    rw [←WilsonMeasuredCompanionTransport.subtract R (N:=N) _ _ left right lo,
      ←WilsonMeasuredCompanionTransport.subtract R (N:=N) _ _ c int lo,field]
  exact ⟨equality,equality ▸ (norm_sub_le ..).trans (add_le_add (numerical R live lo x e n δ s.toList px pe) received)⟩

end YM.Integration.WilsonMeasuredPublicEntranceSignedEar
end
