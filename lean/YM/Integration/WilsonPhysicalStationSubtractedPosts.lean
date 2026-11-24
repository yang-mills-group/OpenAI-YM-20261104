import YM.Integration.WilsonPhysicalStationSubtractedPair

/-! The two elected reporters evaluate the original ordered physical response with its actual lower terminals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationSubtractedPosts
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonMovingForkReporterBothArms (Filed)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)} (J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
  {m k d:ℕ}{I:Type*}[Fintype I]

def heard (hm:d ≤ m)(hk:d ≤ k)(c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label d)
    (u z:(Bel R.family.book).Field d)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) (fun _:Fin 2=>d) j o p.1 p.2
    ![(V k).wheel.atCut p ⟨d,Nat.lt_succ_of_le hk⟩ u-lower R c w p,
      (V m).wheel.atCut p ⟨d,Nat.lt_succ_of_le hm⟩ z]

include F in
theorem voted (hm:d ≤ m)(hk:d ≤ k)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {am bm ak bk:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V d k ak bk)(right:Filed (f:=f) (l:=ℓ) J₀ J V d m am bm)
    (c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label d)(v:I→R.family.label d)
    (converges:∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory d p.1 p.2).terminal (w i p))
      (ℓ:Filter _) (𝓝 (v i)))(u z:(Bel R.family.book).Field d)(j:ℕ)(o:Fin 2 → Cover)
    (safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (heard R V hm hk c w u z j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>d) (Extraction.Order.grid R.family j o) ![J.U k d u-S.project d (∑i,c i • v i),J.U m d z])):=by
  have first:=left ((J₀ (V k).wheel.r d).symm (J.U k d u))
  have second:=right ((J₀ (V m).wheel.r d).symm (J.U m d z))
  dsimp only at first second
  simp only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply] at first second
  obtain ⟨_,X,x,_⟩:=first
  obtain ⟨_,Y,y,_⟩:=second
  have bought:=WilsonPhysicalStationSubtractedPair.original R F simple below X Y c w v converges j o safe
  unfold heard
  simpa only [heard,x,y,heightV,dif_pos hk,dif_pos hm,LinearEquiv.apply_symm_apply] using bought

include F in
theorem original (hm:d ≤ m)(hk:d ≤ k)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {am bm ak bk:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V d k ak bk)(right:Filed (f:=f) (l:=ℓ) J₀ J V d m am bm)
    (c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label d)(v:I→R.family.label d)
    (converges:∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory d p.1 p.2).terminal (w i p))
      (ℓ:Filter _) (𝓝 (v i)))(u z:(Bel R.family.book).Field d)(j:ℕ)(o:Fin 2 → Cover)
    (safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (heard R V hm hk c w ((J.U k d).symm (J₀ (V k).wheel.r d u)) ((J.U m d).symm (J₀ (V m).wheel.r d z)) j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>d) (Extraction.Order.grid R.family j o) ![J₀ (V k).wheel.r d u-S.project d (∑i,c i • v i),J₀ (V m).wheel.r d z])):=by
  simpa only [LinearEquiv.apply_symm_apply] using voted R F J₀ J V hm hk simple below left right c w v converges ((J.U k d).symm (J₀ (V k).wheel.r d u)) ((J.U m d).symm (J₀ (V m).wheel.r d z)) j o safe

end YM.Integration.WilsonPhysicalStationSubtractedPosts
end
