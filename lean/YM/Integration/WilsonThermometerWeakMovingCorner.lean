import YM.Integration.WilsonThermometerWeakCornerPhysical

/-! Mixed readings at two independently shrinking physical radii.  The far
letter is the adjoint of the actually deployed field on the Wilson table. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonThermometerWeakMovingCorner
open Filter Set Function Spec Table Climb PhysMS OPE OPE.Levy Trace.Pilot Extraction Maxwell XSpace XSpace.Normalize
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 PhysicalNext.Repeat.Legato
open WilsonThermometerWeakCornerJets
open scoped Topology BigOperators ContDiff Classical
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→tower S)(V:Store G){n:ℕ}

def far (d:ℕ)(t:ℝ)(e:RG17.Free R.family d): S.Tag :=
  ⟨d,S.adj F.room.kernel.spin d timeAxis (J t d e)⟩

def near (d:Fin n→ℕ)(s:Finset (Fin n))(b:Bool)(r:ℝ)
    (v:∀i,RG17.Free R.family (d i))(i:Fin n):S.Tag :=
  if i∈s then ⟨d i,WilsonNormalizedReflectedForm.field F J V b (d i) r (v i)⟩
    else ⟨d i,S.unit (d i)⟩

theorem original {simple:G.Simple}{L:EveryPhase.Almanac F}(H:Roll.{u} F simple L)
    (lead:Leading F J)(d:Fin n→ℕ)(e k:ℕ)(w:RG17.Free R.family e){A s:ℝ}(ap:0≤A)(sp:0<s):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀(t:ℝ→ℝ),Tendsto t trail trail→∀ᶠ r in trail, r≤t r →
      ∀(x:Points n)(z:E4),
      Pairwise (fun i j=>s*Sum.elim (fun _:Fin n=>r) (fun _:Unit=>t r) i≤
        ‖sites r x (fun _:Unit=>t r • z) i-sites r x (fun _:Unit=>t r • z) j‖)→
      ∀(q:StateIndex F)(M:Finset (Fin n))(b:Bool)(v:∀i,RG17.Free R.family (d i)),
      (∀i,‖v i‖≤A)→
      ‖iteratedFDeriv ℝ k (WilsonThermometerWeakCornerJets.panel F q (near F J V d M b r v) (fun _:Unit=>far F J e (t r) w)
        (fun _:Unit=>t r • z) r) x‖≤C*dock r^m:=by
  obtain ⟨B,m,Bp,pay⟩:=WilsonThermometerWeakCornerNorm.original F H d (fun _:Unit=>e) k sp
  obtain ⟨A₀,Ap,price⟩:=WilsonThermometerWeakCornerSalary.original F J V lead d ap
  obtain ⟨W,Wp,wage⟩:=WilsonNormalizedReflectedForm.uniform F J V lead e (norm_nonneg (reflect e w))
  refine ⟨B*A₀*W,m,mul_nonneg (mul_nonneg (zero_le_one.trans Bp) (zero_le_one.trans Ap)) Wp,?_⟩
  intro t ht
  have small:∀ᶠ u in trail,u≤1:= (ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [price,ht.eventually wage,ht.eventually (lead.equivariant e),self_mem_nhdsWithin,
      ht.eventually small] with r per qfar qr positive ceiling
  intro order x z clear view M b v hv
  have far_eq: (far F J e (t r) w).2=J (t r) e (reflect e w):=
    (PhysMS.Frame.flip_coupled F e J (t r) qr w).symm
  have fw : billSlots F (t r) (fun _:Unit=>far F J e (t r) w)≤W:=by
    rw [billSlots,crestSet,Fintype.prod_unique]
    change cost F e (t r) (far F J e (t r) w).2≤W
    rw [far_eq];exact qfar false _ le_rfl
  have nw:billSlots F r (near F J V d M b r v)≤A₀:=per M b v hv
  have deg (i:Fin n):(near F J V d M b r v i).1=d i:=by
    unfold near;split <;> rfl
  have paid:=pay r ⟨positive,order.trans ceiling⟩ (t r) ⟨order,ceiling⟩ x _ clear view
    (near F J V d M b r v) (fun _:Unit=>far F J e (t r) w) deg (fun _=>rfl)
  have dockpos : 0≤dock r:=by exact zero_le_one.trans (dock_valid r ⟨positive,order.trans ceiling⟩)
  calc _≤B*dock r^m*billSlots F r (near F J V d M b r v)*billSlots F (t r) (fun _:Unit=>far F J e (t r) w):=paid
       _≤B*dock r^m*A₀*W:=mul_le_mul (mul_le_mul_of_nonneg_left nw (mul_nonneg (zero_le_one.trans Bp) (pow_nonneg dockpos _))) fw
          (Finset.prod_nonneg fun i _=>Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (zero_le_one.trans Bp) (pow_nonneg dockpos _)) (zero_le_one.trans Ap))
       _=_:=by ring
end YM.Integration.WilsonThermometerWeakMovingCorner
end
