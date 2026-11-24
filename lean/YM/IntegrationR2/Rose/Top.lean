import YM.IntegrationR2.Rose.Mold
/-!
# Independent coefficients on transported face holonomy v. In true curvature coordinate,
 grade j−2 in action. Pay tail through all finite Taylor orders including on actual torus.
 No launch projection twist. Enough spatial startup bounds to account with existing R using
 its *same* tags. Curvature polynomial is independent of those tags.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Quad.Rose
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

-- index p≥0 actual order through **4+p** in k.
def pre (p:ℕ)(x:G.Color):ℝ:= G05.blockTaylor p (inK G) x
def stub (p:ℕ)(u:G.El):ℝ:= G.price u-pre p (G.curvature u)
private def stubMat (p:ℕ)(a:G.Mat):ℝ:= distMat a-pre p (kMat a)
def column (p:ℕ)(x:G.Color):ℝ:= diagonal (coeff (inK G) p 0) x
lemma reveal (p:ℕ)(x:G.Color): pre (p+1) x=pre p x+column (p+1) x:=by
   unfold pre G05.blockTaylor column; rw [Finset.sum_range_succ]; rfl
lemma reveal4 (u:G.El): stub 4 u=surplus u := by rw [stub,pre,convert_taylor,surplus,sub_add_eq_sub_sub]
lemma peel (p:ℕ) (u:G.El): stub p u=column (p+1) (G.curvature u)+stub (p+1) u := by unfold stub; rw [reveal]; ring
lemma peel' (p:ℕ)(u:G.El): surplus u=(∑ i∈Finset.range p,column (4+i+1) (G.curvature u))+stub (4+p) u := by
   induction p with
   | zero=> simp [reveal4]
   | succ p ih=> rw [ih,peel (4+p)]; rw [Finset.sum_range_succ,Nat.add_assoc 4,add_assoc]
lemma parity (u:G.Color)(p:ℕ)(hp:Odd p): column p u=0:= odd_diagonal u p hp
lemma value_inv (p:ℕ)(x:G.Color): pre p (-x)=pre p x:=G05.blockTaylor_equivariant (inK_diff.of_le le_top) (-ContinuousLinearMap.id ℝ G.Color) (ContinuousLinearMap.id ℝ ℝ) inK_even x
lemma homogeneous (p:ℕ)(t:ℝ)(x:G.Color): column p (t • x)= t^p *column p x:= Tensor.homogeneous (coeff (inK G) p 0) x t
lemma action (p:ℕ)(t:ℝ)(x:G.Color)(ht:t ≠ 0): t⁻¹^2*column (p+2) (t • x)= t^p *column (p+2) x:= by rw [homogeneous,pow_add]; field_simp

def jetTail (G:Gauge)(p:ℕ): Berry G (p+1) where
   f:= stub p
   matP:=stubMat p
   smooth:= by
      have he : ContDiff ℝ ω (distMat (G:=G)) := (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).div_const _
      exact he.sub ((G05.blockTaylor_contDiff ..).comp kMat_diff)
   actual u:= by
      have he:= surplus_actual u; rw [surplusMat,k_actual,surplus] at he; unfold stubMat stub; rw [k_actual]; linarith
   calm u h hm:=by
      have hu : ContinuousAt u 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hm.continuousAt
      let k := fun x=> G.curvature (u x)
      have hz : k 0 = 0 := by simp [k,h,G.curvature_unit]
      refine FlatAt.congr (g := stub p ∘ u)
         (FlatAt.comp (hz.symm ▸ flat_sub_taylor (inK G) p (inK_diff.of_le le_top))
            (u:=k) (by rw [hz]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff .. |>.contDiffAt))
            ((curvature_diff_mat u 0 hm).of_le le_top)) ?_
      filter_upwards [(show Tendsto u (𝓝 0) (𝓝 1) from h ▸ hu.tendsto).eventually (recover_left G)] with x hx
      simp only [comp_apply, Pi.sub_apply, inK,k,hx,stub,pre]
   conjugate u v:= by
      have hh : pre p (G.adjoint u (G.curvature v))=pre p (G.curvature v):= G05.blockTaylor_equivariant (inK_diff.of_le le_top) (G.adjoint u).toContinuousLinearMap (ContinuousLinearMap.id ℝ ℝ) (inK_conjugate u) _
      rw [stub,G.price_conj,G.curvature_conjugate,hh]; rfl
   inv v:= by rw [stub,G.price_inv,G.curvature_inv,value_inv]; rfl

def jetRow (G:Gauge)(θ:ℕ): Berry G (θ+1) :=
   let B:= jetTail G θ; let A:= jetTail G (θ+1)
   { f:=fun u=> B.f u - A.f u
     matP:=fun a=>B.matP a - A.matP a
     smooth:=B.smooth.sub A.smooth
     actual u:=congr_arg₂ (·-·) (B.actual u) (A.actual u)
     calm u h hm:=by
        have h₁ : ContDiffAt ℝ ω (B.f ∘ u) 0:= (B.smooth.contDiffAt.comp _ hm).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x=>(B.actual _).symm))
        have h₂ : ContDiffAt ℝ ω (A.f ∘ u) 0:= (A.smooth.contDiffAt.comp _ hm).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x=>(A.actual _).symm))
        intro k hk; change iteratedFDeriv ℝ k (B.f ∘ u-A.f ∘ u) 0=_; rw [iteratedFDeriv_sub_apply (h₁.of_le le_top) (h₂.of_le le_top), B.calm u h hm k hk,A.calm u h hm k (by omega),sub_self]
     conjugate u v:=congr_arg₂ (·-·) (B.conjugate u v) (A.conjugate u v)
     inv v:=congr_arg₂ (·-·) (B.inv v) (A.inv v) }
lemma read_row (t:ℕ)(u:G.El): (jetRow G t).f u = column (t+1) (G.curvature u):= by
    change stub t u-stub (t+1) u=_; rw [peel t]; ring
end YM.WilsonStartup.Quad.Rose
