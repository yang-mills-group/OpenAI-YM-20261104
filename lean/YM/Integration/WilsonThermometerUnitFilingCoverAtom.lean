import YM.Integration.WilsonThermometerUnitFilingPinnedIncome
import YM.RegulatorIR.Profiles.Aperture

/-! The suspended physical curvature word as an actual finite-range cover portrait. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverAtom
open Function Gauge Lattice Wilson RG QuadraticLocal Marker QuadraticLocal.Earn RegulatorIR RegulatorIR.Halo
open RegulatorIR.Profiles RegulatorIR.Prim PertExtension.Series Finset
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {k:ℕ}
attribute [local instance] Gauge.frobInner

def raw (A:Atom G k) (U:CoverConfig G):ℝ:=A.poly fun i=>(A.leg i).eval U

theorem gauge_slot (a:RG.Slot) (f:Cover → G.El) (U:CoverConfig G):
    a.eval (gauge f U)=G.adjoint (f 0) (a.eval U):=by
  unfold RG.Slot.eval
  rw [travel_gauge,face_gauge,G.curvature_conjugate,← G.adjoint_mul,← G.adjoint_mul]
  simp only [RG.Slot.offset,mul_assoc,inv_mul_cancel,mul_one]

theorem registered (A:Atom G k) (law:A.Invariant):
    LocalStamp (fun _ U=>raw A U) k:=by
  refine ⟨⟨?_,?_,?_⟩,⟨A.stencil,?_⟩,?_⟩
  · change Continuous (fun x:ℝ × CoverConfig G=>
      ∑ s, A.coeff s * ∏ i,(A.leg i).eval x.2 (s i))
    apply continuous_finsetSum
    intro s _
    refine continuous_const.mul (continuous_finsetProd _ fun i _=>?_ )
    exact ((slotPlane (s i)).continuous.comp (A.leg i).cont).comp continuous_snd
  · intro t f U
    simpa only [raw,gauge_slot] using law (f 0) (fun i=>(A.leg i).eval U)
  · intro E _ _ b U h _ _ _
    change ContDiffAt ℝ ∞ (fun t=>∑ s,A.coeff s * ∏ i,(A.leg i).eval (U t) (s i)) 0
    apply ContDiffAt.sum
    intro s _
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_prod
    intro i _
    exact (slotPlane (s i)).contDiffAt.comp _ (sensor U h (A.leg i))
  · intro _ U V h
    apply congrArg A.poly
    funext i
    apply (A.leg i).covered U V
    intro e h₁ h₂
    have inside {x:Cover}(hx:x∈(A.leg i).stencil):x∈A.stencil:=
      Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)
    exact h e (inside h₁) (inside h₂)
  · intro v
    let f (s:Fin k→G.ColorIndex)(i:Fin k)(t:ℝ):ℝ:=(A.leg i).eval (win G (t • v)) (s i)
    have p (s:Fin k→G.ColorIndex):Tested.Bill k (∏ i,f s i):=by
      simpa using Tested.bill_product Finset.univ (fun _:Fin k=>1) (f s)
        (fun i _=>slotCash v (A.leg i) (s i))
    have h (s:Fin k→G.ColorIndex):Tested.Bill k (fun t=>A.coeff s * (∏ i,f s i) t):=by
      simpa using Tested.bill_mul (Tested.bill_const (A.coeff s)) (p s)
    convert Tested.bill_sum Finset.univ _ (fun s _=>h s) using 1
    funext t
    simp only [Halo.outing,raw,RG.Atom.poly,Finset.sum_apply,Finset.prod_apply,f]

def portrait {n:Side} {o:Passport n Unit} {J:Census Unit} {X:Type}
    (T:Row o J G X)(z:Cover)(a:ℝ):Portrait G:=
  convey z (guardP (fun _ U=>raw T.atom U) (fun t=>t^T.lamp.stamp * a))

theorem stamped {n:Side} {o:Passport n Unit} {J:Census Unit} {X:Type}
    (T:Row o J G X)(z:Cover)(a:ℝ) {h:ℕ} (enrolled:h≤T.lamp.toll+1):
    LocalStamp (portrait T z a) h:=by
  have priced:Tested.Bill T.lamp.stamp (fun t:ℝ=>t^T.lamp.stamp * a):=by
    simpa only [smul_eq_mul] using Tested.bill_mon a T.lamp.stamp le_rfl
  have S:=((registered T.atom T.lawful).dresses (f:=fun t:ℝ=>t^T.lamp.stamp*a)
    (by fun_prop) (by fun_prop) priced).moves (t:=z)
  refine ⟨S.people,S.crown,fun v=>Tested.bill_ge (S.order v) ?_⟩
  rw [T.lamp.recovery]
  omega

theorem copied {n n':Side} {o:Passport n Unit} {J:Census Unit} {X:Type}
    (T:Row o J G X)(a g:ℝ)(U:Config G n')(y:Site n'):
    portrait T 0 a g (expandAt y U)=a * QuadraticLocal.Sunrise.Loan.letter T.lamp T.atom y g U:=by
  unfold portrait convey guardP raw QuadraticLocal.Sunrise.Loan.letter RG.Atom.unmasked
  have tz : Lattice.translate 0 (expandAt y U)=expandAt y U:=by
    funext e; simp [Lattice.translate]
  rw [tz]
  simp only [RG.Slot.atSite]
  ring

end YM.Integration.WilsonThermometerUnitFilingCoverAtom
