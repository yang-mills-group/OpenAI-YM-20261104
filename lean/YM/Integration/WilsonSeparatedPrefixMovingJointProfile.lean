import YM.Integration.WilsonSeparatedPrefixMovingJointAddress
import YM.Integration.WilsonSeparatedPrefixMovingAddressInk

/-! Each absolute-center Taylor moment is a genuine compact near profile on the submitted physical sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointProfile
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)
variable {d:ℕ}
def power (w:Fin d→Axis)(p:Point4):ℝ:=∏i,p (w i)
theorem entire (w:Fin d→Axis):ContDiff ℝ ∞ (power w):=by
  apply contDiff_prod
  intro i _
  fun_prop
private lemma finite (D:ℕ)(w:Fin d→Axis):ContDiff ℝ (↑D) (power w):=by
  apply contDiff_prod
  intro i _
  fun_prop
def moment (F:Rarity D)(w:Fin d→Axis):Rarity D where
  ψ:=⟨fun p=>power w p*F.ψ.val p,(finite D w).mul (scribble F.ψ le_rfl)⟩
  radius:=F.radius
  markG:=F.markG
  support:=by
    apply Subset.trans _ F.support
    apply closure_mono
    intro p hp
    change power w p*F.ψ.val p≠0 at hp
    exact (mul_ne_zero_iff.mp hp).2
def addressPower (x y:ℝ)(o:CellR)(s:Cover)(w:Fin d→Axis):Scroll D:=
  ⟨fun p=>power w (Mer.address x y o s p),by
    change ContDiff ℝ (↑D) (power w ∘ Mer.address x y o s)
    apply (finite D w).comp
    unfold Mer.address;fun_prop⟩
theorem row (F:Rarity D)(w:Fin d→Axis)(x y:ℝ)(o:CellR)(s:Cover):
    wheelC x y s (moment F w).ψ o=
      writer (page D (addressPower x y o s w)) (wheelC x y s F.ψ o):=by
  change page D (sonal x y o s _) = writer _ (page D (sonal x y o s _))
  rw [WilsonSeparatedPrefixMovingAddressInk.print]
  rfl
theorem observed (F:Rarity D)(w:Fin d→Axis)(x y:ℝ)(s:Cover)(o z:CellR):
    (moment F w).ψ.val (Mer.address x y o s z.val)=
      (∏i,(Mer.address x y o s z.val) (w i))*F.ψ.val (Mer.address x y o s z.val):=rfl
theorem child (P:Patch)(F:Rarity D)(w:Fin d→Axis)(x y:ℝ)(o:CellR)(s:Cover)(v:Site P.L):
    wheelC x y (heapZ P (s,v)) (moment F w).ψ o=
      foldWord P v D (writer (page D (addressPower (x*P.L.val) y o s w))
        (wheelC (x*P.L.val) y s F.ψ o)):=by
  rw [eyelet,row]
theorem salary (F:Rarity D)(L:ℕ):
    ∃K:ℝ,0≤K ∧ ∀j≤L,∀w:Fin j→Axis,
      (moment F w).radius=F.radius ∧ Amplitude (moment F w) K:=by
  classical
  choose C paid using (fun (j:Fin (L+1))(w:Fin (j:ℕ)→Axis)=>amplitudes (moment F w))
  let K:=∑j:Fin (L+1),∑w:Fin (j:ℕ)→Axis,C j w
  have pp (j:Fin (L+1))(w:Fin (j:ℕ)→Axis):0≤C j w:=(paid j w).1
  refine ⟨K,Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun w _=>pp j w)),?_⟩
  intro j hj w
  let i:Fin (L+1):=⟨j,by omega⟩
  have lw:C i w≤K:=(Finset.single_le_sum (fun t _=>pp i t) (Finset.mem_univ w)).trans
    (Finset.single_le_sum (f:=fun j:Fin (L+1)=>∑w:Fin (j:ℕ)→Axis,C j w)
      (fun j _=>Finset.sum_nonneg (fun w _=>pp j w)) (Finset.mem_univ i))
  exact ⟨rfl,(pp i w).trans lw,fun n hn v x=>((paid i w).2 n hn v x).trans lw⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointProfile
