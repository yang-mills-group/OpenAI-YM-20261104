import YM.Planned.PRIMARY_INTEGRAL_295.Unload
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
import YM.Contacts.Shuttle.Loads
/-!
# Geometry of real radial directions extended to infinite lattice

Avoid taking jets with respect to points outside convergence of formal stencils.
Use finite-dimensional test directions here at every charge; no restriction on
lattice support. Proof adapts PMOM of Signed Source to this situation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open YM.MultiNext.SignedSource Powers Mediator Next.Foundations Pattern Broadcast
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d n m b h k:ℕ}{V W E X I : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
abbrev Stack (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E] (h:ℕ) := (i:Fin (h+1)) → Tensor.T E4 E i.val
def glow (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E] (h:ℕ): Stack E h→ₗ[ℝ](E4→E) where
  toFun f := ∑ i, Tensor.diagonal (f i)
  map_add' f g:= by funext x; simp [Tensor.diagonal,sum_add_distrib]
  map_smul' a f:= by funext x; simp [Tensor.diagonal,smul_sum]
lemma shining (z:E4)(f: Stack E h) : glow E h f z= ∑ i,(f i) (fun _=>z):= Finset.sum_apply z univ (fun i=> Tensor.diagonal (f i))
lemma lit (T:T E4 E n): Powers.home (Tensor.diagonal T) n:= ⟨Tensor.diag_smooth .., fun k x=>Tensor.homogeneous T x k⟩
lemma arrangement : LinearMap.range (glow E h)= Powers.space E4 E h:= by
   apply le_antisymm
   · rintro f ⟨p,rfl⟩; exact (space E4 E h).sum_mem (t:=univ) (fun i _=> residence (lit (p i)) (by omega: (i:Fin (h+1)).val ≤ h))
   apply Submodule.span_le.mpr; rintro f ⟨i,hi,hf⟩; let v:Fin (h+1):= ⟨i,by omega⟩; refine ⟨Pi.single v (Tensor.coeff f i 0),?_⟩
   funext z; rw [shining,Finset.sum_eq_single v]; · rw [Pi.single_eq_same]; exact (congr_fun (Powers.tensor_form hf).symm z) -- Pi.single reduction?
   · intro q _ hh; rw [Pi.single_eq_of_ne hh]; rfl
   simp
structure Stars (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E] (h:ℕ) where
   nodes: Finset E4
   interpolate: (nodes→E) →L[ℝ] Stack E h
   enough (f:E4→E)(hf:f∈ Powers.space E4 E h) : glow E h (interpolate (fun i=> f i))=f
lemma exist (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (h:ℕ): Nonempty (Stars E h):= by
   let L:= glow E h; let X:= LinearMap.range L; let Q(x:E4): X→ₗ[ℝ] E:= (LinearMap.proj x).comp X.subtype
   obtain ⟨v,hv⟩:= Work.A07.finite_rows Q (fun i hi=>Subtype.ext (funext fun j=> hi j)); let A:= LinearMap.pi (fun i:v=> Q i.1); let a:= L.rangeRestrict
   obtain ⟨T,hT⟩:= LinearMap.exists_rightInverse_of_surjective a (by simp [a]); let P:= (T.comp A.leftInverse).toContinuousLinearMap; refine ⟨v,P,fun f hf => ?_⟩
   rw [← arrangement] at hf; let w:X:=⟨f,hf⟩; have he: a (T (A.leftInverse (A w)))=w:=by rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hv)]; exact LinearMap.congr_fun hT _
   exact congr_arg Subtype.val he

def stars (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](h:ℕ) := Nonempty.some (exist E h)
abbrev fit (h:ℕ)(f:E4→E) : Stack E h:= (stars E h).interpolate fun i=> f i
lemma sky {f:E4→E}(hf:f ∈ Powers.space E4 E h): glow E h (fit h f)= f := (stars E h).enough f hf
lemma spot (u:Stack E h): glow E h u ∈ Powers.space E4 E h := by rw [← arrangement]; exact LinearMap.mem_range_self .. 
lemma in_chip (u:Stack E h)(i:ℕ)(h1: u=fit h (glow E h u))(h2: glow E h u∈ Powers.space E4 E i) : ∃ f:E4→E, f∈Powers.space E4 E i∧ u=fit h f:= ⟨_,h2,h1⟩
end YM.Contacts.Shuttle.Tide
