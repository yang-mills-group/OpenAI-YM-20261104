import YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCredit
import YM.Integration.WilsonIndependentMatchedFreshInverseIncome

/-! The forward twenty-one dimensional column budget on the two genuine original cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCourse

open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Matrix PowerSeries Finset
open scoped BigOperators Classical
variable {G:Gauge}{F:Frame G 4}

open WilsonPositionProgramTrialPublicJointFourActiveKernel (watch watched)
open WilsonPositionProgramTrialPublicJointFourActiveCredit (Pass run)
open WilsonIndependentMatchedFreshInverseIncome (age)
variable {D e:ℕ}{T:SectionData F}{fit:4<D}{H:Hol G}{V W Z:Credit}

theorem license (L:Theatre H T fit e V W)(simple:G.Simple)
    (m K N:ℕ)(first:L.V.anchor ≤ m)(window:m ≤ K)(live:K ≤ N):
    Pass (CurNames L.V.draws L.V.paid T fit N m (K-m) false)
      (bindingS L.V.draws L.V.paid T fit N m (K-m) false):=by
  obtain ⟨unit,inv⟩:=ebbing L first (show m+(K-m) ≤ N by omega) false
  have b:=(WilsonPositionProgramTrialPublicJointFourScalarBlock.original L first window live).2.2.2
  refine ⟨inv ▸ Matrix.mul_nonsing_inv _ unit,inv ▸ Matrix.nonsing_inv_mul _ unit,?_,?_⟩
  · intro i j hi hj
    exact b ((WilsonPositionProgramTrialPublicJointFourScalarBlock.crossing i j).2 ⟨hi,hj⟩)
  · intro i j hi
    exact WilsonPositionProgramTrialPublicJointFourGroundRows.original L simple first window live i j hi

def forward (c:CourseS H T fit e V W Z)(t:ℕ):Coil F:=
  CurNames c.vols.draws c.vols.paid T fit t c.spur c.length false

def backward (c:CourseS H T fit e V W Z)(t:ℕ):Coil F:=
  bindingS c.vols.draws c.vols.paid T fit t c.spur c.length false

theorem priced (H:Hol G)(T:SectionData F)(fit:4<D)(e:ℕ)(V W Z:Credit)(simple:G.Simple)(q:ℕ)(depth:q ≤ e):
    ∃C:Credit,∀c:CourseS H T fit e V W Z,∀i j:Alma F,sheet F i ≠ 0 → 
      twain (C.buy c.Age) c.cab (lineS (forward c c.I.n) q i j) (lineS (forward c c.I.N) q i j):=by
  let U:=CourseS H T fit e V W Z
  let x (c:U):=c.Age
  let d (c:U):=c.cab
  have bright:Brite x d:=⟨fun c=>c.I.warm,fun _=>(trail_pos ..).le⟩
  have can (c:U)(t:ℕ)(good:c.tip ≤ t):Pass (forward c t) (backward c t):=by
    simpa [forward,backward,CourseS.tip] using
      license c.robe.arch simple c.spur (c.spur+c.length) t c.root (Nat.le_add_right ..) good
  have incomes j (hj:j ≤ e):CreditsS x d (fun c=>lineS (backward c c.I.n) j) (fun c=>lineS (backward c c.I.N) j):=by
    obtain ⟨B,ear⟩:=glacier H T fit e V W Z false j hj
    intro i s
    exact ⟨B.d,B.x,zero_le_one.trans B.good,fun a=>ear a i s⟩
  have co:=run bright e (fun c=>forward c c.I.n) (fun c=>backward c c.I.n)
    (fun c=>forward c c.I.N) (fun c=>backward c c.I.N)
    (fun c=>can c _ (c.far.trans c.I.hd)) (fun c=>can c _ (c.far.trans c.I.hg)) incomes q depth
  obtain ⟨B,buy⟩:=cashier bright co
  refine ⟨B,fun c i j hi=>?_⟩
  simpa only [watched,if_neg hi] using buy c i j

theorem original (H:Hol G)(T:SectionData F)(fit:4<D)(e:ℕ)(V W Z:Credit)(simple:G.Simple)(q:ℕ)(depth:q ≤ e):
    ∃C:Credit,∀f:ChorusLine H T fit e V W Z,∀m K N:ℕ,f.arch.V.anchor ≤ m → m ≤ K → K ≤ N → 
      ∀i j:Alma F,sheet F i ≠ 0 → 
      ‖lineS (CurNames f.arch.V.draws f.arch.V.paid T fit N m (K-m) false) q i j‖ ≤ 
        C.buy (age f.arch.V.draws f.arch.V.y m K):=by
  obtain ⟨C,paid⟩:=priced H T fit e V W Z simple q depth
  refine ⟨C,?_⟩
  intro f m K N first between live i j hi
  let c:CourseS H T fit e V W Z:=
    ⟨f,⟨f.arch.V,m,K-m,N,N,K,first,by omega,live,live⟩,rfl⟩
  have ar:c.Age=age f.arch.V.draws f.arch.V.y m K:=by
    change _+(f.arch.V.draws.S.scale (m+(K-m))-_) + _=_
    rw [Nat.add_sub_of_le between]
    rfl
  rw [←ar]
  exact (paid c i j hi).main

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCourse
