import YM.RG11Proof.Arrow.Anchor
import YM.RG11Proof.Stress.Shine
import YM.Work.A01.Conserve

/-! # Leading free actual field translations exist and furnish derivative identity
in separated tests -- no independent ψ_lagr answer included. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.RG11.Arrow
open YM.RG11.Fields YM.RG11.Nodes YM.RG11.Jets
open scoped Classical BigOperators Topology ContDiff
open Function Maxwell Labels Table Climb Analysis Filter Pert.Position MeasureTheory Set
open PowerSeries
variable {G:Gauge}(F:Frames G){d n:ℕ}(B:Adapted F d)(C:Adapted F (d+1)){ι:B.toBasis.J↪ C.toBasis.J}

private def writer {n}(v:Fin n→E F d):Fin n→ (freeTable F).Tag:=Sigma.mk d ∘ v

@[simp] private theorem sees_at (x:Points n)(v:Fin n→E F d):visible F d x v=(freeTable F).useAt (freeTable F) x (writer F v):=rfl
private theorem sees_diff(v:Fin n→E F d):ContDiffOn ℝ ∞ (fun x=>visible F d x v) (conf n):=
   (freeTable F).class_smooth _ (table_smooth F) (writer F v)

lemma ascent (i:B.toBasis.J)(h:Adapted.Gives B C (Nat.le_succ d) ι):
    Free.address F (d+1) (C.b (ι i)) = Free.address F d (B.b i):=by
   have he (d:ℕ)(z:E F d): Free.address F d z=Extra.FD.writes F d z:=by
     obtain ⟨q,rfl⟩ := (freeTable F).onto d z
     rw [Free.address_eval,Free.fields_eval,Extra.FD.writes_project]; rfl
   rw [he,h,up_write,he]

private theorem at_points (a:Axis)(h:Adapted.Gives B C (Nat.le_succ d) ι)(i:B.toBasis.J)(v:Fin n→C.toBasis.J){x:Points (n+1)}(hx:x∈conf _):
   visible F (d+1) x (Fin.cons (α:=fun _:Fin (n+1)=> E F (d+1)) ((Free.scheme F).deriv d a (B.b i)) (C.b ∘ v))=
      Points.gradient (n:=n+1) 0 a (fun y=>visible F (d+1) y (Fin.cons (α:=fun _:Fin (n+1)=>E F (d+1)) (C.b (ι i)) (C.b ∘ v))) x:=by
   let w:=C.b ∘ v
   have ht i : C.b (ι i)= (Free.scheme F).rise (Nat.le_succ d) (B.b i):=Free.address_inj F (d+1) (by rw [Free.address_rise,ascent F B C i h])
   simp_rw [sees_at,writer, Work.A01.comp_cons]; rw [(Free.scheme_derives F).kernels _ _ _ hx,ht]
   unfold Points.gradient D
   rw [Filter.EventuallyEq.fderiv_eq]
   filter_upwards [(conf_open (n+1)).mem_nhds hx] with y hy
   exact ((Free.scheme_filters F).kernels (Nat.le_succ d) (B.b i) hy (Sigma.mk (d+1) ∘ (C.b ∘ v))).symm

private theorem CD_direction {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](K:V→ℂ){s:Set V}(ho:IsOpen s)(h:ContDiffOn ℝ ∞ K s)(v:V): ContinuousOn (fun x=>fderiv ℝ K x v) s:=by
   have he:=h.continuousOn_fderivWithin ho.uniqueDiffOn (by simp)
   have H:ContinuousOn (fun x=>fderivWithin ℝ K s x v) s:=he.clm_apply (show ContinuousOn (fun _=>v) s from continuousOn_const)
   exact H.congr (fun x hx=>by dsimp only; rw [fderivWithin_of_mem_nhds (ho.mem_nhds hx)])

-- patch IBP transfer
 theorem hand (K:Points n→ℂ)(hK:ContDiffOn ℝ ∞ K (conf n))(i:Fin n)(a:Axis)(t:Test n): t.applyTo (Points.gradient i a K)=(plans a i t).applyTo K:=by
   unfold Test.applyTo; change (∫ x, t x*fderiv ℝ K x (Points.direction i a))=_
   simp_rw [plans_at,Points.gradient,D,neg_mul,integral_neg]
   refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ (t.smearing hK.continuousOn) (fun x _=> t.contDiff.differentiable (by simp) x) (fun x hx=>hK.differentiableOn (by simp) x (t.tsupport_subset hx) |>.differentiableAt ((conf_open _).mem_nhds (t.tsupport_subset hx)))
   · have he:= (plans a i t).smearing hK.continuousOn
     simp_rw [plans_at,Points.gradient,D,neg_mul] at he
     simpa using he.neg
   apply t.smearing
   exact CD_direction _ (conf_open _) hK _

def rootStep : lane B.toBasis C.toBasis:=fun a=>Matrix.of fun i j=> PowerSeries.C (C.toBasis.coord ((Free.scheme F).deriv d a (B.b i)) j)

 theorem begins (h:Adapted.Gives B C (Nat.le_succ d) ι)(A:ShapeReport G F):Arrives A B.toBasis C.toBasis ι (rootStep F B C) 0:=by
   rintro a f w i k hk; obtain rfl:k=0:=Nat.eq_zero_of_le_zero hk
   unfold armed question rootStep
   simp_rw [Matrix.of_apply,map_sum,coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_C,ShapeReport.price0]
   let Q:E F (d+1):=(Free.scheme F).deriv d a (B.b i)
   have he : Basis.overReals Q:=(Free.phase_orientation F).realDer _ _ _ |>.trans (congrArg _ (B.pinned i))
   let v:=C.b ∘ w
   have hl : (∑ j, C.toBasis.coord Q j * rowZero C.toBasis (⟨⟨2,f⟩,Fin.cons (α:=fun _:Fin 2=> C.toBasis.J) j w⟩))=(wickReading F (d+1) f (Fin.cons (α:=fun _:Fin 2=> E F (d+1)) Q v)).re:=by
       let M := wickReading F (d+1) f
       nth_rw 2 [← C.toBasis.put_round Q he]
       simp_rw [Basis.put_sum]
       change (∑ j, _ * rowZero C.toBasis _) = (M.curryLeft _ v).re
       rw [map_sum,_root_.sum_apply]; simp_rw [map_smul,_root_.smul_apply,smul_eq_mul,Complex.re_sum,Complex.re_ofReal_mul]
       apply Finset.sum_congr rfl; intro j _; unfold rowZero
       change _ * (M (C.b ∘ Fin.cons (α:=fun _:Fin 2=>C.toBasis.J) _ _)).re = _*(M (Fin.cons (α:=fun _:Fin 2=> E F (d+1)) _ _)).re
       rw [Work.A01.comp_cons]
   change _= rowZero C.toBasis _; rw [hl]
   unfold wickReading rowZero
   dsimp only [MultilinearMap.coe_mk]
   apply congrArg Complex.re
   rw [f.apply_eq (fun x hx=>at_points F B C a h i w hx),hand _ (sees_diff F _) 0 a f]
   change _ = (plans a 0 f).applyTo (fun y=>visible F _ y (C.b ∘ Fin.cons (α:=fun _:Fin 2=>C.toBasis.J) _ _)); rw [Work.A01.comp_cons]
end YM.RG11.Arrow
