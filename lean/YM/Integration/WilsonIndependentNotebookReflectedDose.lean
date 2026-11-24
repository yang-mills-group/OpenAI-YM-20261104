import YM.Integration.WilsonIndependentNotebookReflectedFilm
import YM.Integration.WilsonIndependentNotebookDoseCoefficients

/-! The reflected full field and its measured pivot on the original report and held clocks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedDose
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Wheel.Motion
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonPositionProgramTrialStationHome (Seated)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonPositionProgramTrialFittedLens (matrix)
open scoped BigOperators Classical
variable {G:Gauge}{h k e D N m K i u d:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}{A B:Credit}

def axes (F:Labels.Frame G h)(s:Signed):Wall F:=Matrix.of fun i j=>blueIn F s i j

theorem coefficients (s:Signed)(c:Verse F):Cosmos.paintC F s*ᵥc=matrix (axes F s) c:=by
  funext i
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def]
  rfl

theorem transported (L:Theatre H T p e A B)(hm:L.V.anchor ≤ m)(hn:m+i ≤ N)(s:Signed)(v:Verse F):
    street L.V.draws L.V.paid T p N m i (Cosmos.paintC F s*ᵥv)=
      Cosmos.paintC F s*ᵥstreet L.V.draws L.V.paid T p N m i v:=by
  have recal:Chars F (relativeF L.V.draws L.V.paid N m i) (Cosmos.paintC F s)=Cosmos.paintC F s:=
    Matrix.ext fun _ _=>reel_C ..
  unfold street
  rw [turnV,recal,mulVec_mulVec,mulVec_mulVec,Names_spin L hm hn]
  
theorem seated (R:Run G)(W:Initialize G)(Q:SealR G)(rails:Rails Q.h k u e)
    (kind:Bool)(dim:d<Q.D)(cap:d ≤ k)(s:Signed)(v:Verse (R.family.labels.level d))(b:ℝ)
    (X Y:CutsP (hol G) Q.ans Q.path rails Credit.leanC Credit.leanC Credit.leanC Credit.leanC)
    (aX aY:ℝ)
    (one:Seated R Q rails m K N (b • Shrine (plate (sectionAt R W kind d) dim) v) aX X)
    (two:Seated R Q rails m K N
      (b • Shrine (plate (sectionAt R W kind d) dim) (Cosmos.paintC (R.family.labels.level d) s*ᵥv)) aY Y):
    let S:=axes Q.F s
    let M:=Wray R.family.path.levels R.metals.O Q.ans Q.path N m
    ∀a:ℝ,dose Y a=matrix S (dose X a) ∧
      publicDose Q Y a=matrix (M*S*M⁻¹) (publicDose Q X a):=by
  intro S M a
  obtain ⟨ax,ox,mx,kx,nx,_,px,_⟩:=one
  obtain ⟨ay,oy,my,ky,ny,_,py,_⟩:=two
  have ir:Y.i=X.i:=by
    have dx:X.m+X.i=K:=kx
    have dy:Y.m+Y.i=K:=ky
    omega
  let U:=Cosmos.paintC Q.F s
  obtain ⟨l,r,given⟩:=WilsonIndependentNotebookReflectedFilm.named R W kind dim cap s v b
  have h:=WilsonIndependentNotebookReflectedTally.original X.L.L s X.ha
    (Nat.le_add_right X.m X.i) (X.hc.trans X.hn) rails.hk l r given
  have prim:Y.tileP=U*ᵥX.tileP:=by
    change tallyV Y.ax Y.tx Q.ans Q.path Y.N k Y.ceilC Y.m Y.pt=
      U*ᵥtallyV X.ax X.tx Q.ans Q.path X.N k X.ceilC X.m X.pt
    rw [ay,oy,ky,my,ny,py,ax,ox,kx,mx,nx,px]
    change tallyV X.ax X.tx Q.ans Q.path X.N k X.ceilC X.m _=U*ᵥtallyV X.ax X.tx Q.ans Q.path X.N k X.ceilC X.m _ at h
    simpa only [ax,ox,kx,mx,nx] using h
  have st:=transported X.L.L X.ha (X.hc.trans X.hn) s (a • X.tileP)
  have same:dose Y a=U*ᵥdose X a:=by
    change street Y.ax Y.tx Q.ans Q.path Y.N Y.m Y.i (a • Y.tileP)=
      U*ᵥstreet X.ax X.tx Q.ans Q.path X.N X.m X.i (a • X.tileP)
    rw [prim,←mulVec_smul,ir,ay,oy,my,ny,ax,ox,mx,nx]
    simpa only [ax,ox,mx,nx] using st
  have dc:dose Y a=matrix S (dose X a):=same.trans (coefficients s _)
  refine ⟨dc,?_⟩
  have inv:= (WilsonPositionProgramTrialHomeDose.original Q X a).1
  change matrix (Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ (publicDose Q X a)=dose X a at inv
  change matrix (Wray Y.ax Y.tx Q.ans Q.path Y.N Y.m) (dose Y a)=_
  rw [ax,ox,nx,mx] at inv
  rw [ay,oy,ny,my,dc,←inv]
  rw [WilsonPositionProgramTrialFittedLens.compose,WilsonPositionProgramTrialFittedLens.compose]

end YM.Integration.WilsonIndependentNotebookReflectedDose
