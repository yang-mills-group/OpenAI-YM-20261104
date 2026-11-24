import YM.OPE.Compatible.Spades.Heel
/-!
# Color grammar
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
section
local notation "J"=> Bid.Dir G n
def shadesP (u:G.El):Bid.Dir G n ≃ₗ[ℝ] Bid.Dir G n:={
       toFun x i:= G.adjoint u (x i)
       invFun x i:= G.adjoint u⁻¹ (x i)
       map_add' x y:=funext fun i=>map_add (G.adjoint u) (x i) (y i)
       map_smul' c x :=funext fun i=>map_smul (G.adjoint u) c (x i)
       left_inv x:=funext fun i=>(show G.adjoint u⁻¹ (G.adjoint u (x i))=x i from (G.adjoint_mul ..).symm.trans (by simp))
       right_inv x:=funext fun i=>(show G.adjoint u (G.adjoint u⁻¹ (x i))=x i from (G.adjoint_mul ..).symm.trans (by simp)) }
def folio (A:Mat (Body 1 n))(x: Bid.Dir G n): J:=fun i=> ∑ j,A i j • x j
lemma Muler (A:Mat (Body 1 n))(x:Bid.Dir G n): flatten (folio A x)=tensor G A*ᵥflatten x:=by
       funext i; obtain ⟨i,j,t⟩:=i; change folio A x (i,j) t=component (tensor G A*ᵥ _) t (i,j); rw [component_mul,folio]; change chin t _=_; rw [map_sum];rfl
lemma folHue (v:G.El)(A:Mat (Body 1 n))(x: Bid.Dir G n): folio A (shadesP v x)= shadesP v (folio A x):=by
       funext i; change _= G.adjoint v (∑ j,A i j • x j); rw [map_sum]; exact Finset.sum_congr rfl fun j _=> (map_smul (G.adjoint v) (A i j) (x j)).symm
lemma folioD (v:G.El)(A:Mat (Body 1 n))(x y:Bid.Dir G n): flatten (shadesP v x) ⬝ᵥ( tensor G A*ᵥ flatten (shadesP v y))= flatten x ⬝ᵥ( tensor G A*ᵥ flatten y):=by
       rw [← Muler,← Muler, folHue, FreeResolvent.flat_dot, FreeResolvent.flat_dot]; exact Finset.sum_congr rfl fun j _=> (by apply Variance.hubAD -- in dot?
                                                                             ) -- edit
noncomputable def rotaryB (G:Gauge)(b:ℕ)(v:G.El):Scoop G b→L[ℝ] Scoop G b:= (strideG G b).toContinuousLinearMap ∘L ((crevy v) ∘L (strideG G b).symm.toContinuousLinearMap)
lemma zodiac (v:G.El)(b:ℕ)(x:Bid.Dir G n): Cane G b o (shadesP v x)= rotaryB G b v (Cane G b o x):=by
       have hz: ascJ o (flats G n (shadesP v x))=plumeX v (ascJ o (flats G n x)):=by rw [flatX,flatX]; rfl
       change strideG G b (socket b (InLine _ (ascJ o (flats G n (shadesP v x)))))= strideG G b (crevy v ((strideG G b).symm (strideG G b (socket b (InLine _ (ascJ o (flats G n x)))))))
       rw [hz,loopletB, chive,ContinuousLinearEquiv.symm_apply_apply]
lemma clans (u:G.El)(v:Train i) (h:4 ≤ i)(K:KernelChoices)(b:ℕ): let B:=Vessel K v G n h; let S:= Cane G b o; Chip B S (rotaryB G b u ∘L S) B:=by
       intro B S; let T:= rotaryB G b u; let Y:=(shadesP u (n:=n)); have hh(x:J): B.P x x=B.P (Y x) (Y x):=by
            have hx (x:J):B.P x x=_:=(Hport K v G n h).choose_spec.2 x x; rw[hx,hx,flatX,flatX]; exact (folioD u _ x x).symm
       constructor; intro i j
       have he(k : Dual' (Scoop G b)): ((k.comp S.toLinearMap).comp Y.toLinearMap)= k.comp ((T ∘L S).toLinearMap):=LinearMap.ext fun i=> congr_arg k (zodiac o u b i)
       change _=B.wick _ _; rw[← (dual_wick Y B B hh (i.comp _) (j.comp _)),he,he] -- danger rw all wick
end
end YM.OPE.Spells
