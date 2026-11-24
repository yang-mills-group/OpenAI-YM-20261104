import YM.RG06.Continuum.ConnectionJets
import YM.Pert.Align.Span
import YM.Pert.Lattice.Recovery
import YM.Source.Local

/-!
# Eq. Jrad nonlinear contraction

Along a radial ray, z·A(tz) vanishes identically, so *ordered* iterated covariant directional
derivatives in the constant direction z may be computed by ordinary ray derivatives. Contract the
curvature and use homogeneous polynomials to evaluate the exact coefficient in this germ;
no flat-curvature approximation and no gauge or equation-of-motion identities required. This is
why the independent (unconstrained, even Bianchi/EOM-redundant) covariance slots can represent
all radial labels, with the correct normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Labels Maxwell Tensor Lattice
open scoped BigOperators ContDiff Topology Classical InnerProductSpace
variable {G : Gauge}

def Radial (A:Connection G):Prop := ∀ x:E4, ∑ i:Axis, x i • A i x=0

variable (g:ℝ)(A:Connection G)

def along (z:E4)(f:Continuum.Section G) : Continuum.Section G:=∑ i:Axis, z i • covariant g A i f

def powers (z:E4) (j:ℕ)(f:Continuum.Section G) : Continuum.Section G:= match j with
  | 0=>f
  | k+1=> along g A z (powers z k f)

lemma work (h:Smooth A)(z:E4)(f:Continuum.Section G)(hf:Good f)(j:ℕ): Good (powers g A z j f):=by
  induction j with
  | zero=>exact hf
  | succ j H=>
    change Good (∑ i:Axis, z i • covariant g A i (powers g A z j f))
    let p (i:Axis): Continuum.Section G:= z i • covariant g A i (powers g A z j f)
    rw [show (∑ i:Axis,z i • covariant g A i (powers g A z j f))=fun x=>∑ i, p i x from funext (fun x=> Finset.sum_apply ..)]
    exact ContDiff.sum (fun i _=> ContDiff.const_smul (z i) (Smooth.connection g A h i _ H))

lemma point_along (z:E4)(f:Continuum.Section G)(x : E4) :
    along g A z f x = D z f x + g • G.ad (∑ i:Axis, z i • A i x) (f x):=by
  have hz : ∑ i:Axis,z i • basis i=z := by ext i; simp [WithLp.ofLp_sum,Finset.sum_apply,basis,Pi.single_apply, mul_ite]
  unfold along covariant par D; rw [Finset.sum_apply]
  simp only [Pi.smul_apply,Pi.add_apply, smul_add, Finset.sum_add_distrib,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply, Finset.smul_sum]
  congr 1
  · conv_rhs=> arg 2; rw [← hz]
    rw [map_sum]; simp only [map_smul]
  exact Finset.sum_congr rfl fun i _=> smul_comm ..

-- ray alignment exact even at t=0 if the connection is zero there (true for the polynomial radial samples).
lemma along_radial (z:E4)(t:ℝ)(f:Continuum.Section G)(h:Radial A)(h0:∀ i,A i 0=0): along g A z f (t • z)=D z f (t • z):=by
  have he : ∑ i:Axis, z i • A i (t • z)=0:= by
    by_cases ht:t=0
    · simp [ht,h0]
    have hh:=h (t • z); apply smul_right_injective G.Color ht
    simp only [PiLp.smul_apply] at hh
    change t • (∑ i:Axis,z i • A i (t • z)) = t • 0; rw [Finset.smul_sum,smul_zero]; simp_rw [smul_smul]; exact hh
  rw [point_along g A, he,map_zero]; simp

lemma along_eq (h:Smooth A)(z:E4)(f:Continuum.Section G)(hf:Good f)(j:ℕ)(r:Radial A)(hr:∀ i,A i 0=0) :
    (fun t:ℝ=>powers g A z j f (t • z))= iteratedDeriv j (fun t:ℝ=> f (t • z)):=by
  induction j with
  | zero=> rw [iteratedDeriv_zero]; rfl
  | succ j H=>
    rw [iteratedDeriv_succ,← H]; funext t
    change along g A z (powers g A z j f) _ = _; rw [along_radial g A z t _ r hr]
    let L:ℝ→L[ℝ]E4:= (ContinuousLinearMap.id ℝ ℝ).smulRight z
    rw [show (fun t:ℝ=> powers g A z j f (t • z))=powers g A z j f ∘ L from rfl]
    unfold deriv D; rw [fderiv_comp t ((work g A h _ _ hf j).germ (L t)) L.differentiableAt,L.fderiv]; simp [L]

lemma par_lincombo {I:Type*} (s:Finset I)(c:I→ℝ)(f:I→Continuum.Section G)(i:Axis)(h:∀ q∈s,Good (f q)) :
    par i (∑ q∈s,c q • f q)=∑ q∈s,c q • par i (f q):=by
  induction s using Finset.induction with
  | empty=>rw [Finset.sum_empty,Finset.sum_empty];funext x;simp [par,D]
  | insert a s ha H=>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,par_add]
    · rw [par_scale _ (h _ (Finset.mem_insert_self ..)),H (fun i hi=>h i (Finset.mem_insert_of_mem hi))]
    · exact ContDiff.const_smul (c a) (h a (Finset.mem_insert_self ..))
    let p (q:I): Continuum.Section G:=c q • f q
    rw [show (∑ i∈s,c i • f i)=fun x=>∑ i∈s,p i x from funext (fun x=> Finset.sum_apply ..)]
    exact ContDiff.sum (fun i hi=> ContDiff.const_smul (c i) (h i (Finset.mem_insert_of_mem hi)))

lemma cov_lincombo {I:Type*}(s:Finset I)(c:I→ℝ)(f:I→Continuum.Section G)(i:Axis)(h:∀ q∈s,Good (f q)):
    covariant g A i (∑ q∈s,c q • f q)= ∑ q∈s,c q • covariant g A i (f q):=by
  unfold covariant; rw [par_lincombo _ _ _ _ h]
  simp_rw [smul_add, Finset.sum_add_distrib]; congr 1; funext x
  simp only [Finset.sum_apply, bracket, Pi.smul_apply,map_sum,map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _=> smul_comm ..

lemma axis_expand (z:E4)(j:ℕ)(f:Continuum.Section G)(h:Smooth A)(hf:Good f):
    powers g A z j f= ∑ w:Fin j→ Axis,(∏ i,z (w i)) • nablas g A w f:=by
  induction j with
  | zero=>rw [Fintype.sum_subsingleton _ (Fin.elim0 (α:= Axis))]; simp only [Finset.univ_eq_empty, Finset.prod_empty,one_smul,nablas]; rfl
  | succ j H=>
     -- split words by head
     let e:(Fin (j+1)→Axis)≃ Axis×(Fin j→Axis):=
       {toFun w:=(w 0,Fin.tail w)
        invFun w:=Fin.cons w.1 w.2
        left_inv w:= by simp
        right_inv w:=by simp}
     rw [← Equiv.sum_comp e.symm (fun w=> (∏ i,z (w i)) • nablas g A w f), Fintype.sum_prod_type]
     rw [powers,H,along]
     refine Finset.sum_congr rfl fun i _=> ?_
     rw [cov_lincombo (h:=fun w _=> Smooth.higherCov g A h w f hf), Finset.smul_sum]
     refine Finset.sum_congr rfl fun w _=> ?_
     change z i • ((∏ i,z (w i)) • covariant g A i (nablas g A w f))=
       (∏ a:Fin (j+1), z (Fin.cons (α:=fun _=>Axis) i w a)) • nablas g A (Fin.cons (α:=fun _=>Axis) i w) f
     rw [Fin.prod_univ_succ,nablas,Fin.cons_zero,Fin.tail_cons,smul_smul]; simp
lemma covariant_neg (q:Continuum.Section G) (i:Axis) : covariant g A i (-q)= -covariant g A i q:=by unfold covariant; rw [par_neg]; funext; simp [bracket,add_comm]
lemma cov_skew {j:ℕ}(x:E4)(w:Fin j→Axis)(i b:Axis): covJet g A w b i x= - covJet g A w i b x := by
  have he(q:Continuum.Section G)(j:ℕ)(w:Fin j→Axis): nablas g A w (-q) = - nablas g A w q:= by
    induction j with
    | zero=> rfl
    | succ j H=> rw [nablas,nablas,H,covariant_neg]
  unfold covJet; rw [show curvature g A b i =-curvature g A i b from funext fun x=>skew ..,he]; simp

section radial
variable {j:ℕ}(d:ℕ)(v:Labels.Jet G)

def radField : Connection G:= Source.potential d v
lemma rad_smooth : Smooth (radField d v):=fun i=> (show ContDiff ℝ ∞ (fun x=>∑ j∈Finset.range (d-1), diagonal ((v j).1 i) x) from ContDiff.sum fun j _=> Tensor.diag_smooth (v j|>.val i) _)
@[simp] lemma rad_zero (i:Axis) : radField d v i 0=0:=by
  unfold radField Source.potential Labels.Taylor.value Tensor.diagonal
  apply Finset.sum_eq_zero
  intro j _; rw [ContinuousMultilinearMap.map_coord_zero (i:=(0:Fin (j+1)))];rfl
lemma rad_taxi :Radial (radField d v):=fun z=>by
  unfold radField Source.potential; simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_eq_zero fun j _=> Taylor.radial_value ..

lemma cov_along_linear (t:ℝ)(p:Labels.Taylor G j)(z:E4)(a b:Axis):
    par a (p.value b) (t • z)= t^j • par a (p.value b) z:=by
  unfold par D Taylor.value
  simp only [Tensor.differential_diagonal _ (p.property.1 _)]
  have he := Tensor.homogeneous ((p.val b).curryLeft (basis a)) z t
  simp only [Tensor.diagonal] at he
  rw [he, ← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ,smul_comm]

lemma radial_curl (p:Labels.Taylor G j)(z:E4)(a:Axis):
    ∑ k:Axis,z k • (par k (p.value a) z - par a (p.value k) z)= ((j+2:ℕ):ℝ) • p.value a z:=by
  have he:= Maxwell.grad_self p.val a z
  rw [show (fun z=>∑ k:Axis, z k • diagonal (p.val k) z)=(0:E4→G.Color) from
    funext (fun z=>p.property.2 z)] at he
  have H := show p.value a z + ∑ k : Axis,z k • par a (p.value k) z = 0 from (show (0:G.Color)=_ from by simpa [Maxwell.grad,D] using! he).symm -- elaboration
  have hh:= Maxwell.grad_euler (p.val a) (p.property.1 a) z
  simp only [smul_sub,Finset.sum_sub_distrib]
  rw [show ∑ k:Axis,z k • par k (p.value a) z = _ from hh,
     show ∑ k:Axis,z k • par a (p.value k) z = -p.value a z from eq_neg_of_add_eq_zero_right H,sub_neg_eq_add]
  change ((j+1:ℕ):ℝ) • p.value a z + p.value a z = _
  nth_rw 2 [← one_smul ℝ (p.value a z)]
  rw [← add_smul]; congr 1; push_cast; ring

lemma par_rad (a b:Axis):par a (radField d v b)= ∑ j∈Finset.range (d-1),par a ((v j).value b):=by
  have h:radField d v b= ∑ j∈Finset.range (d-1),(1:ℝ) • (v j).value b:=by funext; unfold radField Source.potential; rw [Finset.sum_apply]; simp
  rw [h,par_lincombo]; simp
  exact fun j _=> Tensor.diag_smooth ((v j).val b) _

lemma rayEquation (z:E4)(a:Axis)(t:ℝ):
    (∑ k:Axis,z k • curvature g (radField d v) k a (t • z)) =
      ∑ j∈ Finset.range (d-1), (t^j) • (((j+2:ℕ):ℝ) • (v j).value a z):=by
  let A:= radField d v
  have hr:∑ k:Axis,z k • A k (t • z)=0:=by
    by_cases h:t=0
    · simp [h,A]
    have he:=rad_taxi d v (t • z)
    apply smul_right_injective G.Color h
    change t • (∑ i:Axis,z i • A i (t • z)) = _; simp_rw [Finset.smul_sum,smul_smul]; simp only [PiLp.smul_apply] at he -- beneath sum
    simpa using he
  have hc:(∑ k:Axis,z k • g • bracket (A k) (A a) (t • z))=0:=by
    have he : g • G.ad (∑ i:Axis,z i • A i (t • z)) (A a (t • z))=0:=by rw [hr,map_zero];simp
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply, Finset.smul_sum, smul_comm g] at he
    exact he
  unfold curvature
  simp only [Pi.add_apply,Pi.smul_apply,smul_add,Finset.sum_add_distrib]
  rw [hc,add_zero]
  simp_rw [par_rad, Pi.neg_apply,Finset.sum_apply,smul_neg]
  rw [← Finset.sum_add_distrib];
  simp_rw [Finset.smul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  rw [Finset.sum_comm];
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← sub_eq_add_neg,cov_along_linear,smul_comm _ (t^i),← smul_sub,← Finset.smul_sum] -- smul inside z
  rw [radial_curl]

-- degree j term, exact equality, same Probe/scaling conventions as Recovery
lemma radial_exact (z:E4)(a:Axis)(j:ℕ)(h:j < d-1):
    (∑ i:Axis,z i • ∑ w:Fin j→Axis,(∏ k:Fin j,z (w k)) • covJet g (radField d v) w i a 0)=
      ((j+2:ℕ):ℝ) • (v j).value a z:=by
  let A:=radField d v
  have hA:=rad_smooth d v
  let X(i:Axis):=curvature g A i a
  let Y(i:Axis)(t:ℝ):=X i (t • z)
  let t:ℝ→L[ℝ] E4:= (ContinuousLinearMap.id ℝ ℝ).smulRight z
  have hY (i):ContDiff ℝ ∞ (z i • Y i):=
    ContDiff.const_smul (z i) (ContDiff.comp (Smooth.F g A hA i a) (f:=fun s:ℝ=>s • z) (contDiff_id.smul contDiff_const)) -- Good alias .comp fails
  have he i: (∑ w:Fin j→Axis, (∏ k,z (w k)) • nablas g A w (X i) 0)= iteratedDeriv j (Y i) 0:=by
    have hp := congr_fun (along_eq g A hA z (X i) (Smooth.F g A hA i a) j (rad_taxi d v) (rad_zero d v)) 0
    change powers g A z j (X i) (0 • z)=_ at hp
    rw [zero_smul,axis_expand g A z j _ hA (Smooth.F g A hA i a), Finset.sum_apply] at hp; exact hp
  unfold covJet
  simp_rw [smul_comm _ ((j.factorial:ℝ)⁻¹),← Finset.smul_sum]
  simp_rw [smul_comm _ ((j.factorial:ℝ)⁻¹),← Finset.smul_sum]
  change (j.factorial:ℝ)⁻¹ • (∑ i:Axis, z i • ∑ w:Fin j→Axis, (∏ k,z (w k)) • nablas g A w (X i) 0)=_
  simp only [he,show ∀ i:Axis,z i • iteratedDeriv j (Y i) 0= iteratedDeriv j (z i • Y i) 0 from fun i=> (iteratedDeriv_const_smul_field ..).symm]; rw [← iteratedDeriv_sum (by exact fun i _=> (hY i).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  rw [show (∑ i:Axis, z i • Y i)=fun t=>∑ i∈Finset.range (d-1), t^i • (((i+2:ℕ):ℝ) • (v i).value a z) from funext (fun t=> (Finset.sum_apply ..).trans (rayEquation g d v z a t))]
  let V(i:ℕ):=((i+2:ℕ):ℝ) • (v i).value a z
  have hd(i:ℕ):ContDiffAt ℝ j (fun t:ℝ=> t^i • V i) 0:= (contDiffAt_id.pow i).smul contDiffAt_const
  change (j.factorial:ℝ)⁻¹ • iteratedDeriv j (fun t=> ∑ i∈_, t^i • V i) 0=_
  rw [iteratedDeriv_fun_sum (by exact fun i _=>hd i)] -- expects he with _
  have hc(i:ℕ) : iteratedDeriv j (fun t:ℝ=>t^i • V i) 0= if j=i then (j.factorial:ℝ) • V i else 0:= by
    rw [iteratedDeriv_smul_const,iteratedDeriv_fun_pow_zero]; split_ifs with he <;> simp [*,V]
    exact contDiffAt_id.pow _
  simp_rw [hc, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr h),smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero (R:=ℝ)|>.mpr j.factorial_ne_zero),one_smul]
  rfl

/-- Reuse accepted `radialize` on a nonlinear input: no shell restriction, exact Jrad instead
of just its known linearization `complete`. -/
def panel {j:ℕ}(x:E4): Pert.Bare.Response G j:= fun i k w=>covJet g (radField d v) w i k x
lemma reconstruct (j:ℕ)(h:j+2 ≤ d): Pert.Bare.radialize (panel g d v (j:=j) 0)=v j:=by
  apply Taylor.value_ext
  funext i z
  rw [Pert.Bare.radial_value]
  have hp(b:Axis)(w:Fin j→Axis):(1/2:ℝ) • (panel g d v 0 b i w - panel g d v 0 i b w)=covJet g (radField d v) w b i 0:=by
    unfold panel; rw [cov_skew g _ 0 w b i]; -- occurrence
    rw [sub_neg_eq_add,← two_smul ℝ,smul_smul];norm_num
  simp_rw [hp]
  rw [radial_exact _ _ _ _ _ _ (by omega),smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
end radial
end YM.RG06.Continuum
