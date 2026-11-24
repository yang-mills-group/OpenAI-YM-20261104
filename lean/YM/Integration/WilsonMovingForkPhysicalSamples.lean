import YM.Integration.WilsonMovingForkExactHomes
import YM.Integration.WilsonMovingForkProfileSamples
import YM.Integration.WilsonMovingForkSameEpochResidual

/-! The actual normalized product and all of its output-field matrix
entries on the same real outer field. The two signed tests buy separate
finite point sets, chosen before the physical cutoffs. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMovingForkPhysicalSamples
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O MS MS.Land MS.Theater
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPositionIntegrals WilsonMovingForkProbeMaster WilsonMovingForkProbeDates
open WilsonMovingForkLocalReceipt (physical)
open WilsonPublicForkPublicRows (probe)
open private kernel from YM.Integration.WilsonPublicForkInterchange
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){n h:ℕ}(d:Fin n→ℕ)(v:∀i,Free R.family (d i))
    (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ})(ψ:Test n)

theorem original (j:B.probes.index){ε:ℝ}(ep:0<ε):
    let φ:=profile (B.probes.shell j) (w j) (issued j) (test B j)
    let a:=probe B w
    let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued t.property.1 j
    let basis:=WilsonMSDictionaryVector.basis R.family h
    let pub:=homogeneous F J Z r.val
    let Y:=RG17.appeared F (d:=d) (fun i=>pub (d i) (v i)) X r.val ψ
    let M:=fun k=>X.charge F h (pub h (basis k))
    let obs (p:Points n×Points 2):=S.useAt S (placed r.val t.val p.1 (relative p.2))
      (physical F J Z (bound d) (dose d v a) (dates r t) (WilsonMovingForkProbeMaster.whole j))
    let row (k:Dframe.Toon G h) (z:Points 2):=S.useAt S (t.val • z)
      (physical F J Z (bound d) (dose d v a) (dates r t) (pair k j))
    (∀x∈tsupport ψ,∀z∈tsupport φ,placed r.val t.val x (relative z)∈conf (n+1)) →
    ∃ι:Type,∃_:Fintype ι,∃x:ι→space ψ φ,∃μ:ι→ℂ,∃κ:Type,∃_:Fintype κ,∃z:κ→tsupport φ,∃ν:κ→ℂ,
       (∑i,‖μ i‖)≤Read.Value ψ*Read.Value φ+ε ∧ (∑b,‖ν b‖)≤Read.Value φ+ε ∧
       ‖Y-∑i,μ i*obs (x i)‖≤ε ∧ (∀k,‖M k-∑b,ν b*row k (z b)‖≤ε) ∧
       ∀c:Dframe.Toon G h→ℂ,‖(Y-∑k,c k*M k)-((∑i,μ i*obs (x i))-∑k,c k*∑b,ν b*row k (z b))‖≤
         ε+∑k,‖c k‖*ε:=by
  intro φ a X basis pub Y M obs row safe
  have eqY:Y=tested ψ φ obs:=by
    have same:(fun i=>pub (d i) (v i))=fun i=>J r.val _ (active F J Z r.val (d i) (v i)):=by
      funext i;simp only [pub,active,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
    dsimp only [Y];rw [same]
    change RG17.appeared F _ (stencil J φ t.property.1 _) r.val ψ=_
    rw [WilsonMovingForkPhysicalProducts.whole F J ψ φ t.property.1 _ _ safe]
    dsimp only [obs];rw [WilsonMovingForkProbeDates.whole F J Z]
    rfl
  have eqM(k:Dframe.Toon G h):M k=φ.applyTo (row k):=by
    dsimp only [M,X,row]
    rw [WilsonMovingForkProbeDates.gram F J Z,WilsonPublicOutputSmooth.charge F J Z B w issued t.property.1]
    change WilsonMatrixTicketLanesSmearedRows.observation F J Z _ (test B j) t.val h (pub h (basis k))=_
    rw [WilsonMacroscopicRichPositionRows.output F J Z _ (w j) (issued j) _ t.property.1]
    apply congrArg φ.applyTo;funext u
    let H:=twoTags F J h Z r.val t.val (a j) k
    change S.read (t.val • u) _=S.read (t.val • u) (fun i:Fin 2=>⟨(H i).1,S.representative _ (H i).2⟩)
    apply congrArg (S.read (t.val • u));funext i;fin_cases i <;> rfl
  have wholePaid:ContinuousOn obs (space ψ φ):=fun p hp=>(kernel F _ p (safe p.1 hp.1 p.2 hp.2)).continuousWithinAt
  have pairPaid(k):ContinuousOn (row k) (tsupport φ):=by
    apply (S.class_smooth S F.room.kernel.smooth _).continuousOn.comp (continuous_const_smul _).continuousOn
    exact fun u hu=>Work.A05.smul_conf t.property.1 (φ.tsupport_subset hu)
  obtain ⟨ι,finite,x,μ,upper,full⟩:=WilsonMovingForkProfileSamples.joint ψ φ (fun _:Unit=>obs) (fun _=>wholePaid) ep
  obtain ⟨κ,census,z,ν,money,gram⟩:=WilsonMovingForkProfileSamples.one φ row pairPaid ep
  have y:‖Y-∑i,μ i*obs (x i)‖≤ε:=eqY ▸ full ()
  have m(k):‖M k-∑b,ν b*row k (z b)‖≤ε:=eqM k ▸ gram k
  refine ⟨ι,finite,x,μ,κ,census,z,ν,upper,money,y,m,?_⟩
  intro c
  let M' k:=∑b,ν b*row k (z b)
  have pay:‖∑k,c k*(M k-M' k)‖≤∑k,‖c k‖*ε:=(norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (m k) (norm_nonneg _))
  change ‖(Y-∑k,c k*M k)-((∑i,μ i*obs (x i))-∑k,c k*M' k)‖≤_
  rw [show (Y-∑k,c k*M k)-((∑i,μ i*obs (x i))-∑k,c k*M' k)=
    (Y-∑i,μ i*obs (x i))-∑k,c k*(M k-M' k) by simp_rw [mul_sub];rw [Finset.sum_sub_distrib];abel]
  exact (norm_sub_le _ _).trans (add_le_add y pay)

end YM.Integration.WilsonMovingForkPhysicalSamples
end
