import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reports
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.RealSectors
open YM YM.Maxwell YM.XSpace.Normalize
variable {G:Gauge}{d:ℕ}

theorem fixed (v:Sec G d):reel d v=v ↔ ∀m,(MvPolynomial.coeff m v.val).im=0:=by
  constructor
  · intro h m
    have k:=congrArg (fun p:WickPol G=>(MvPolynomial.coeff m p).im) (congrArg Subtype.val h)
    change (MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) v.val)).im=_ at k
    rw [MvPolynomial.coeff_map] at k
    change -(MvPolynomial.coeff m v.val).im=(MvPolynomial.coeff m v.val).im at k
    linarith
  · intro h
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    change MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) v.val)=_
    rw [MvPolynomial.coeff_map]
    apply Complex.ext
    · rfl
    · change -(MvPolynomial.coeff m v.val).im=(MvPolynomial.coeff m v.val).im
      rw [h,neg_zero]

def conjugate (T:FieldEnd G d):FieldEnd G d where
  toFun v:=reel d (T (reel d v))
  map_add' _ _:=by simp only [map_add]
  map_smul' a v:=by simp only [map_smulₛₗ,starRingEnd_apply,star_star,RingHom.id_apply]

theorem commutes {T:FieldEnd G d}(h:∀v,reel d v=v → reel d (T v)=T v):
    ∀v,T (reel d v)=reel d (T v):=by
  have eq:(coeS d).comp T=(coeS d).comp (conjugate T):=by
    apply real_tests
    intro v hv
    change (T v).val=(reel d (T (reel d v))).val
    rw [hv,h v hv]
  intro v
  apply Subtype.ext
  have hh:=DFunLike.congr_fun eq (reel d v)
  change (T (reel d v)).val=(reel d (T (reel d (reel d v)))).val at hh
  rwa [reel_back] at hh

theorem original (T:FieldEnd G d):
    (∀v,T (reel d v)=reel d (T v)) ↔
    ∀v:Sec G d,(∀m,(MvPolynomial.coeff m v.val).im=0)→
      ∀m,(MvPolynomial.coeff m (T v).val).im=0:=by
  constructor
  · intro h v hv
    exact (fixed _).mp ((h v).symm.trans (congrArg T ((fixed _).mpr hv)))
  · intro h
    exact commutes fun v hv=>(fixed _).mpr (h v ((fixed _).mp hv))
end IssuedMaxwell.RealSectors
end
