import YM.Integration.WilsonPositionProgramTrialPublicJointFourScalarBlock
import YM.Integration.WilsonPositionProgramTrialPublicJointFourLive
import YM.Integration.WilsonPositionProgramTrialFittedTable
import YM.Integration.WilsonPositionProgramTrialGradeRuler
import YM.Integration.WilsonPhysicalSixWickRows

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundRows
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k:ℕ}{F:Frame G 4}{T:SectionData F}{p:4<D}{H:Hol G}

open WilsonPositionProgramTrialPublicJointFourScalarBlock (band crossing)
open WilsonPositionProgramTrialFittedTable (change ground)
open scoped BigOperators Matrix

/-- A change of finite rows fixing the nonunit outputs can be removed on a block
whose complete scalar sector stays scalar. -/
private theorem compare {ι:Type*}[Fintype ι][DecidableEq ι] (active:ι→Prop)
    (M B K F:Matrix ι ι ℝ)(same:M*B=F*K)(unit:IsUnit K.det)
    (older:∀i,active i→∀x:ι→ℝ,(M*ᵥx) i=x i)
    (newer:∀i,active i→∀x:ι→ℝ,(K*ᵥx) i=x i)
    (block:∀i,active i→∀j,¬active j→B i j=0)
    (i:ι)(lit:active i)(x:ι→ℝ):(B*ᵥx) i=(F*ᵥx) i:=by
  classical
  let y:=K⁻¹*ᵥx
  have it:K*ᵥy=x:=by unfold y;rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ unit,Matrix.one_mulVec]
  have fixed j (hj:active j): y j=x j:=by rw [←newer j hj y,it]
  calc
    _ = (B*ᵥy) i:=by
      apply Finset.sum_congr rfl
      intro j _
      change B i j*x j=B i j*y j
      by_cases hj:active j
      · rw [fixed j hj]
      · rw [block i lit j hj,zero_mul,zero_mul]
    _ = (M*ᵥ(B*ᵥy)) i:=(older i lit _).symm
    _ = (F*ᵥx) i:=by rw [Matrix.mulVec_mulVec,same,←Matrix.mulVec_mulVec,it]

def office (T:SectionData F)(p:4<D):SealR G:={h:=4,D:=D,F:=F,ans:=T,path:=p}

theorem original {e m K N:ℕ}{E W:Credit}(L:Theatre H T p e E W)(simple:G.Simple)
    (admitted:L.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)(i j:Alma F)(active:sheet F i≠0):
    let A:=L.V.draws
    let O:=L.V.paid
    lineS (CurNames A O T p N m (K-m) false) 0 i j=(1:Wall F) i j:=by
  classical
  intro A O
  let Q:=office T p
  let C:=CurNames A O T p N m (K-m) false
  have block:= (WilsonPositionProgramTrialPublicJointFourScalarBlock.original L admitted before live).2.2.1
  have kept (k l:Alma F)(hk:sheet F k≠0)(hl:sheet F l=0):lineS C 0 k l=0:=by
    have zero:C k l=0:=block ((crossing k l).2 ⟨hk,hl⟩)
    simp [lineS,zero]
  by_cases seen:sheet F j=0
  · have different:i≠j:=by
      intro eq
      apply active
      rw [eq]
      exact seen
    rw [kept _ _ active seen,Matrix.one_apply_ne different]
  let P:=identum (forwardW A O T p N m (K-m))
  have first:Wray A O T p N m * lineS C 0=P*Wray A O T p N K:=by
    exact ground H Q L admitted before live
  have un:IsUnit (Wray A O T p N K).det:=wick_unit _ (production L live (admitted.trans before)).1 _ _
  have reduce:=compare (fun a=>sheet F a≠0) _ (lineS C 0) _ P first un
    (fun a ha=>WilsonPhysicalSixWickRows.nonunit L (by decide) simple (before.trans live) admitted a ha)
    (fun a ha=>WilsonPhysicalSixWickRows.nonunit L (by decide) simple live (admitted.trans before) a ha)
    (fun k hk l hl=>kept k l hk (not_not.mp hl)) i active (Pi.single j 1)
  have eq:lineS C 0 i j=P i j:=by simpa [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite] using reduce
  have top (a:Alma F)(ha:sheet F a≠0):weight F a=4:=by
    obtain ⟨degree,rank⟩:=WilsonPositionProgramTrialPublicJointFourLive.grades F simple (by decide) a ha
    change (F.grades (sheet F a)).1+rankS (notar F a)=4
    rw [degree,rank]
  have fd:=WilsonPositionProgramTrialGradeRuler.signed H Q L admitted before live i j (by
    change weight F i ≤ weight F j;rw [top i active,top j seen])
  change P i j*(A.S.a K/A.S.a m)^(4-weight F j)=(1:Wall F) i j at fd
  rw [top j seen,Nat.sub_self,pow_zero,mul_one] at fd
  exact eq.trans fd

end YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundRows
