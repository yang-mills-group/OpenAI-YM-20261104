import YM.Integration.WilsonIndependentPrimitiveOrbit
import YM.Integration.WilsonIndependentPrimitiveCoordinates

/-! Translation of the true ordinary primitive sum with all relative period images. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveStroll
open Function Filter Lattice Laurent Bloch RG Wilson RegulatorIR RegulatorIR.Oracle RegulatorIR.Profiles
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Diagram RegulatorIR.Budget
open RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Binding
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentSpoutFiniteStencil (Raw Keys fold)
open WilsonIndependentSpoutOrdinaryPrimitives (board liftKey project back)
open WilsonIndependentPrimitiveTranslations (roots)
open WilsonIndependentPrimitiveOrbit (shiftK shiftV wrap_shift)
open WilsonIndependentConditionalNativeLinks (joint)
open WilsonIndependentPrimitiveCoordinates (printed jo)
open scoped BigOperators Classical

def liftPerm {I X:Type}(V:Equiv.Perm X):Equiv.Perm (I→X):={
  toFun:=fun x=>V∘x
  invFun:=fun x=>V.symm∘x
  left_inv:=fun x=>funext fun j=>V.symm_apply_apply (x j)
  right_inv:=fun x=>funext fun j=>V.apply_symm_apply (x j) }

def cell {G:Gauge}(P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))(e r:ℕ)(z:Branchix):=
  Stalk.collect (fun k:Tuple (KFoot G) r=>fold P n∘k) (T z e r)

theorem cellMove {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(n:Side)(v:Cover)(z:Branchix)(e r:ℕ)
    (x:Fin r→Raw G (n*(C.pactP f).L)⊕Raw G n):
    let P:=C.pactP f;let T:=C.bore G Z t f
    cell P n T e r (roots P v z) (shiftV P n v∘x)=cell P n T e r z x:=by
  intro P T
  let S:=C.rail K f
  have hv:=congr_fun (WilsonIndependentPrimitiveTranslations.original C Z t f v z e) r
  change T (roots P v z) e r=echo (bundleS S v) (T z e r) at hv
  unfold cell
  rw [hv]
  apply WilsonIndependentPrimitiveOrbit.collect
    (fun k:Tuple (KFoot G) r=>fold P n∘k) (liftPerm (bundleS S v)) (liftPerm (shiftV P n v))
    (fun a=>funext fun j=>wrap_shift S n v (a j))

theorem vanished (n:Side)(v:Cover):wrap n (n.val • v)=0:=by
  rw [map_nsmul];funext i
  change n.val • (wrap n v) i=0
  rw [nsmul_eq_mul];simp [Per]

theorem period {G:Gauge}(P:Patch)(n:Side)(v:Cover)(x:Raw G (n*P.L)⊕Raw G n):
    shiftV P n (n.val • v) x=x:=by
  rcases x with ⟨⟨u,a⟩,i⟩|⟨⟨u,a⟩,i⟩
  · change Sum.inl ((wrap (n*P.L) (P.L.val • (n.val • v))+u,a),i)=_
    rw [show P.L.val • (n.val • v)=(n*P.L).val • v by rw [smul_smul,Nat.mul_comm];rfl,
      vanished,zero_add]
  change Sum.inr ((wrap n (n.val • v)+u,a),i)=_
  rw [vanished,zero_add]

theorem full {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(n:Side)(v:Cover)(e r:ℕ)
    (x:Fin r→Raw G (n*(C.pactP f).L)⊕Raw G n):
    let P:=C.pactP f;let T:=C.bore G Z t f
    board P n T e r (shiftV P n v∘x)=board P n T e r x:=by
  intro P T
  have transfer (i:Keys P n):cell P n T e r (liftKey (shiftK P n v i)) (shiftV P n v∘x)=
      cell P n T e r (liftKey i) x:=by
    let j:=roots P v (liftKey i)
    obtain ⟨w,hw⟩:=WilsonIndependentPrimitiveOrbit.deck P n
      (x:=j) (y:=liftKey (shiftK P n v i)) (by rw [WilsonIndependentSpoutOrdinaryPrimitives.back];unfold j;rw [WilsonIndependentPrimitiveOrbit.project_shift,WilsonIndependentSpoutOrdinaryPrimitives.back])
    rw [hw]
    have atDeck:=cellMove C Z t f n (n.val • w) j e r (shiftV P n v∘x)
    change cell P n T e r (roots P (n.val • w) j) (shiftV P n (n.val • w)∘(shiftV P n v∘x))=cell P n T e r j (shiftV P n v∘x) at atDeck
    rw [show (shiftV P n (n.val • w)∘(shiftV P n v∘x))=shiftV P n v∘x from
      funext fun k=>period P n w _] at atDeck
    exact atDeck.trans (cellMove C Z t f n v (liftKey i) e r x)
  simp only [WilsonIndependentSpoutOrdinaryPrimitives.board,Finset.sum_apply]
  exact Fintype.sum_equiv (shiftK P n v).symm _ _ fun i=>by simpa only [cell,Equiv.apply_symm_apply] using transfer ((shiftK P n v).symm i)

theorem readMove {G:Gauge}{c d:Side}(S:StepData d c)(n:Side)(v:Cover)(x:Raw G (n*S.patch.L)⊕Raw G n):
    jo G S.patch n (shiftV S.patch n v x)=jog (wrap n v) (jo G S.patch n x):=by
  have full:Surjective (fold (G:=G) S.patch n):=by
    rintro (⟨⟨z,a⟩,i⟩|⟨⟨z,a⟩,i⟩)
    · exact ⟨Sum.inl ((lift z,a),i),congr_arg (fun t=>Sum.inl ((t,a),i)) (wrap_lift z)⟩
    exact ⟨Sum.inr ((lift z,a),i),congr_arg (fun t=>Sum.inr ((t,a),i)) (wrap_lift z)⟩
  obtain ⟨z,rfl⟩:=full x
  rw [←wrap_shift,WilsonIndependentPrimitiveCoordinates.wrapping,WilsonIndependentPrimitiveCoordinates.translation,
    fold_move,WilsonIndependentPrimitiveCoordinates.wrapping]

theorem original {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(n:Side)(e r:ℕ):
    stroll (printed (C.pactP f) (C.bore G Z t f) e r n):=by
  intro v x
  let P:=C.pactP f;let T:=C.bore G Z t f
  have h:=full C Z t f n (lift v) e r ((jo G P n).symm∘x)
  convert h using 1
  apply congr_arg (board P n T e r)
  funext j
  apply (jo G P n).injective
  change jo G P n ((jo G P n).symm (jog v (x j)))=jo G P n (shiftV P n (lift v) ((jo G P n).symm (x j)))
  have h:=readMove (C.rail K f) n (lift v) ((jo G P n).symm (x j))
  change jo G P n (shiftV P n (lift v) ((jo G P n).symm (x j)))=jog (wrap n (lift v)) (jo G P n ((jo G P n).symm (x j))) at h
  rw [h];simp only [wrap_lift,Equiv.apply_symm_apply]
  rfl

end YM.Integration.WilsonIndependentPrimitiveStroll
