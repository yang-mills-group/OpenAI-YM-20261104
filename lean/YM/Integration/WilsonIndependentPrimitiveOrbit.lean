import YM.Integration.WilsonIndependentPrimitiveTranslations
import YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives

/-! Each original translated bond is reindexed in its own fibre of the full physical period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveOrbit
open RegulatorIR.Profiles WilsonCoeffUV.Bank
open Function Filter Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Prim
open RegulatorIR.Geometry RegulatorIR.Diagram
open WilsonIndependentPrimitiveTranslations (root roots)
open WilsonIndependentSpoutFiniteStencil (Raw Keys coordinates fold)
open WilsonIndependentSpoutOrdinaryPrimitives (board liftKey project back)
open scoped BigOperators Classical

theorem collect {X Y:Type}(π:X→Y)(s:Equiv.Perm X)(t:Equiv.Perm Y)
    (ht:∀x,π (s x)=t (π x))(u:X→ℝ)(h:Y):
    Stalk.collect π (u∘s.symm) (t h)=Stalk.collect π u h:=by
  let E:Stalk π h≃Stalk π (t h):={
    toFun:=fun x=>⟨s x,(ht x).trans (congr_arg t x.property)⟩
    invFun:=fun x=>⟨s.symm x,t.injective (by rw [←ht,s.apply_symm_apply];exact x.property)⟩
    left_inv:=fun x=>Subtype.ext (s.symm_apply_apply _)
    right_inv:=fun x=>Subtype.ext (s.apply_symm_apply _) }
  unfold Stalk.collect
  rw [←E.tsum_eq]
  apply tsum_congr
  intro x
  exact congr_arg u (s.symm_apply_apply _)

def shiftK (P:Patch)(n:Side)(v:Cover):Equiv.Perm (Keys P n):=
  (jog (wrap (n*P.L) (P.L.val • v))).sumCongr (jog (wrap n v))

def shiftV {G:Gauge}(P:Patch)(n:Side)(v:Cover):Equiv.Perm (Raw G (n*P.L)⊕Raw G n):=
  ((jog (wrap (n*P.L) (P.L.val • v))).prodCongr (Equiv.refl _)).sumCongr
    ((jog (wrap n v)).prodCongr (Equiv.refl _))

theorem project_shift (P:Patch)(n:Side)(v:Cover)(x:Branchix):
    project P n (roots P v x)=shiftK P n v (project P n x):=by
  rcases x with ⟨z,a⟩|⟨z,a⟩
  · exact congr_arg (fun t=>Sum.inl (t,a)) ((wrap (n*P.L)).map_add _ _)
  exact congr_arg (fun t=>Sum.inr (t,a)) ((wrap n).map_add _ _)

theorem wrap_shift {G:Gauge}{c d:Side}(S:StepData d c)(n:Side)(v:Cover)(x:KFoot G):
    fold S.patch n (bundleS S v x)=shiftV S.patch n v (fold S.patch n x):=by
  rcases x with ⟨⟨z,a⟩,b⟩|⟨⟨z,a⟩,b⟩
  · exact congr_arg (fun t=>Sum.inl ((t,a),b)) ((wrap (n*S.patch.L)).map_add _ _)
  exact congr_arg (fun t=>Sum.inr ((t,a),b)) ((wrap n).map_add _ _)

theorem fibre (n:Side){x y:Cover}(h:wrap n x=wrap n y):∃v:Cover,y=n.val • v+x:=by
  have d (i:Axis):(n.val:ℤ)∣ y i-x i:=(ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congr_fun h i)
  obtain ⟨v,hv⟩:=Classical.axiomOfChoice d
  refine ⟨v,funext fun i=>?_⟩
  change y i=(n.val:ℤ)*v i+x i
  exact sub_eq_iff_eq_add.mp (hv i)

theorem deck (P:Patch)(n:Side){x y:Branchix}(eq:project P n x=project P n y):
    ∃v:Cover,y=roots P (n.val • v) x:=by
  rcases x with ⟨x,a⟩|⟨x,a⟩<;> rcases y with ⟨y,b⟩|⟨y,b⟩
  · obtain ⟨v,h⟩:=fibre (n*P.L) (congr_arg Prod.fst (Sum.inl.inj eq))
    have hb:a=b:=congr_arg Prod.snd (Sum.inl.inj eq)
    refine ⟨v,congr_arg Sum.inl (Prod.ext ?_ hb.symm)⟩
    change y=P.L.val • (n.val • v)+x
    change y=(n.val*P.L.val) • v+x at h
    simpa only [smul_smul,Nat.mul_comm] using h
  · cases eq
  · cases eq
  obtain ⟨v,h⟩:=fibre n (congr_arg Prod.fst (Sum.inr.inj eq))
  exact ⟨v,congr_arg Sum.inr (Prod.ext h (congr_arg Prod.snd (Sum.inr.inj eq)).symm)⟩

end YM.Integration.WilsonIndependentPrimitiveOrbit
