import YM.Integration.WilsonIndependentSpoutPrimitiveWindow

/-! A fixed positive-rank coordinate of the original emitted additive bank
sums only the enrolled links whose true finite stencil contains that coordinate. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPrimitiveFronts
open Lattice RG RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration Tree
open WilsonIndependentSpoutPrimitiveWindow
open scoped Classical BigOperators

private theorem first (E:Finset (Edge Cover)):rangeE 0 E=E:=by
  classical
  unfold rangeE
  have id':dis 0=(id:Edge Cover→Edge Cover):=by funext z;exact Prod.ext (zero_add _) rfl
  rw [id',Finset.image_id]

private theorem farther (x y:Cover)(E:Finset (Edge Cover)):rangeE x (rangeE y E)=rangeE (x+y) E:=by
  classical
  unfold rangeE
  rw [Finset.image_image]
  congr 1
  funext e
  exact Prod.ext (add_assoc _ _ _).symm rfl

theorem shifted (P:Patch)(q:Cover)(v:Axis):lantern P (q,v)=rangeE (P.L.val • q) (lantern P (0,v)):=by
  classical
  have union (x:Cover)(V E:Finset (Edge Cover)):rangeE x (V∪E)=rangeE x V∪rangeE x E:=Finset.image_union ..
  have cover {J:Type}[DecidableEq J](x:Cover)(S:Finset J)(a:J→Finset (Edge Cover)):
      rangeE x (S.biUnion a)=S.biUnion (fun j=>rangeE x (a j)):=by
    classical
    ext z
    simp only [rangeE,Finset.mem_image,Finset.mem_biUnion]
    aesop
  simp only [lantern,smul_zero,zero_add,first,union,cover,farther,smul_add]

private theorem optical (P:Patch):Function.Injective (fun q:Cover=>P.L.val • q):=by
  intro x y h
  funext j
  have eq:=congr_fun h j
  have hn:(P.L.val:ℤ)≠0:=by exact_mod_cast P.L.property.ne'
  apply mul_left_cancel₀ hn
  simpa only [Pi.smul_apply,nsmul_eq_mul] using eq

theorem lower (P:Patch)(v:Axis)(edge:Edge Cover):{q:Cover|edge∈lantern P (q,v)}.Finite:=by
  classical
  let origins:Finset Cover:=(lantern P (0,v)).image (fun x=>edge.1-x.1)
  have S:(fun q:Cover=>P.L.val • q) ⁻¹' (origins:Set Cover) |>.Finite:=
    origins.finite_toSet.preimage (optical P).injOn
  apply S.subset
  intro q h
  change edge∈lantern P (q,v) at h
  rw [shifted,rangeE] at h
  obtain ⟨a,inside,eq⟩:=Finset.mem_image.mp h
  apply Finset.mem_image.mpr
  refine ⟨a,inside,?_⟩
  have e:=congr_arg Prod.fst eq
  change P.L.val • q+a.1=edge.1 at e
  rw [←e,add_sub_cancel_right]

theorem finite {G:Gauge}(P:Patch)(z:KFoot G):{b:Branchix|z∈sites G P b}.Finite:=by
  classical
  cases z with
  | inl z=>
    let E:Finset Branchix:=insert (.inl z.1) (Finset.univ.biUnion fun v:Axis=>
      (lower P v z.1).toFinset.image fun q:Cover=>Sum.inr ((q,v):Edge Cover))
    apply E.finite_toSet.subset
    rintro (a|a) h <;> simp only [Set.mem_setOf_eq,sites] at h
    · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp h
      have ca:a=z.1:=congr_arg Prod.fst (Sum.inl.inj eq)
      exact Finset.mem_insert.mpr (Or.inl (congr_arg Sum.inl ca))
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨a.2,Finset.mem_univ _,Finset.mem_image.mpr ⟨a.1,?_,rfl⟩⟩
      apply (lower P a.2 z.1).mem_toFinset.mpr
      rcases Finset.mem_union.mp h with hf|hc
      · obtain ⟨x,hx,hz⟩:=Finset.mem_image.mp hf
        have eq:x=z:=Sum.inl.inj hz
        exact eq ▸ (Finset.mem_product.mp hx).1
      · obtain ⟨x,_,hz⟩:=Finset.mem_image.mp hc
        contradiction
  | inr z=>
    apply (Set.finite_singleton (Sum.inr z.1:Branchix)).subset
    rintro (a|a) h <;> simp only [Set.mem_setOf_eq,sites] at h
    · obtain ⟨j,_,h⟩:=Finset.mem_image.mp h
      contradiction
    · rcases Finset.mem_union.mp h with hf|hc
      · obtain ⟨j,_,h⟩:=Finset.mem_image.mp hf
        contradiction
      · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp hc
        exact congr_arg Sum.inr (congr_arg Prod.fst (Sum.inr.inj eq))

def fronts {G:Gauge}(P:Patch)(z:KFoot G):Finset Branchix:=(finite P z).toFinset

theorem original {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (e r:ℕ)(q:Tuple (KFoot G) r)(pin:Fin r):
    ((C.dialect Y G Z (sheet D)).frames f).addon e r q=
      ∑ b∈fronts (C.pactP f) (q pin),C.bore G Z (sheet D) f b e r q:=by
  change (∑'b,C.bore G Z (sheet D) f b e r q)=_
  apply tsum_eq_sum
  intro b hb
  apply selected C Z D f b e r q pin
  intro he
  exact hb ((finite (C.pactP f) (q pin)).mem_toFinset.mpr he)

end YM.Integration.WilsonIndependentSpoutPrimitiveFronts
