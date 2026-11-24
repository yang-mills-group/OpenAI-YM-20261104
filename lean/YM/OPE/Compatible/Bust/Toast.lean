import YM.OPE.Compatible.Bust.Moral
/-!
# W common linear sym phase. Ad contraction gradient
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
def magicL (G:Gauge)(N:Side)(u:G.El):Matrix (FreeResolvent.Slot G N 1) (FreeResolvent.Slot G N 1) ℝ:= LinearMap.toMatrix' ((deckW G N).symm.toLinearMap ∘ₗ (Cascade.Grid.hueL u N).toLinearMap ∘ₗ (deckW G N).toLinearMap)
lemma magicB (u:G.El)(x:Vec G N 1): magicL G N u*ᵥ x= chipHue u x:=LinearMap.toMatrix'_mulVec ..
lemma chip_rev (u:G.El)(x:Vec G N 1): chipHue u (chipHue u⁻¹ x)=x:=by
     let D:=deckW G N; let w:=D x; have h(p:Tab (Shade G) N): hue u (hue u⁻¹ w) p=w p:=by
          let Y:G.Color:= WithLp.toLp 2 (fun i=> w (p.1,p.2.1,i)); change G.adjoint u (G.adjoint u⁻¹ Y) p.2.2= Y p.2.2; rw [show G.adjoint u (G.adjoint u⁻¹ Y)=Y from G.colorMat_injective (by rw [G.mat_adjoint,G.mat_adjoint,G.conjugate_inv])]
     unfold chipHue; rw [LinearEquiv.apply_symm_apply, funext h, LinearEquiv.symm_apply_apply]
lemma chip_charge (u:G.El)(x y:Vec G N 1): chipHue u x ⬝ᵥ chipHue u y=x ⬝ᵥ y:=by
     let f(v:Vec G N 1)(p:Body 1 N):G.Color:=WithLp.toLp 2 fun i=>component v i p; have ht(v:Vec G N 1): v=flatten (f v):=rfl
     have he(v:Vec G N 1)(p): f (chipHue u v) p= G.adjoint u (f v p):=by ext i; exact congr_fun (plume_chip u v i) _
     calc
      _= ∑ p:Body 1 N, inner ℝ (f (chipHue u x) p) (f (chipHue u y) p):= flat_dot (f (chipHue u x)) (f (chipHue u y))
      _= ∑ p:Body 1 N, inner ℝ (f x p) (f y p):=sum_congr rfl fun p _=>by rw [he,he]; exact (show G.Color →ₗᵢ[ℝ] G.Color from ⟨G.adjoint _, G.norm_adjoint _⟩).inner_map_map _ _ -- name
      _= _ := (flat_dot (f x) (f y)).symm
lemma magic_cov (u:G.El)(v:Train r)(X:KernelChoices)(n:Side): magicL G n u* PhV X v G n*(magicL G n u)ᵀ= PhV X v G n:=by
     let M:= magicL G n u
     apply Matrix.ext_of_mulVec_single; intro i; let t: Vec G n 1:= Pi.single i 1
     have he(x:Vec G n 1): Mᵀ*ᵥ x= chipHue u⁻¹ x:=by
          suffices h:Mᵀ*ᵥ x-chipHue u⁻¹ x=0 from sub_eq_zero.mp h
          apply decides; intro y; rw [dotProduct_sub,sub_eq_zero,entrusted,transpose_transpose,magicB]; exact (congr_arg ((chipHue u y) ⬝ᵥ ·) (chip_rev u x).symm).trans (chip_charge ..)
     rw [← mulVec_mulVec,← mulVec_mulVec,he t,magicB, PhV, chromatic,chip_rev]
variable {p:Seat k (m+1) (Shade G)}
lemma arcing (A:Song (Vec G N 1))(i:ℕ)(u:G.El)(v:Train r) (K: KernelChoices)(hp: (pulling (magicL G N u) A) (i+2) = A (i+2)): pulling (magicL G N u) (opus (PhV K v G N) A) i= opus (PhV K v G N) A i:=by
      let Z:= magicL G N u; let X:= PhV K v G N; change ((wind i • Semester X (A (i+2))).compContinuousLinearMap (fun _=>climbs Z))=wind i • Semester X (A (i+2)); conv_rhs=> rw [← hp]
      have hz:Semester X ((pulling Z A) (i+2))= (Semester X _).compContinuousLinearMap (fun _=> climbs Z):=columnAlong X X Z (magic_cov u v K N).symm (A (i+2)); rw [hz]; rfl
end YM.OPE.Silt.Float
