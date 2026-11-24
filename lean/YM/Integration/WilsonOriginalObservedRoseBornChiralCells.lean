import YM.Integration.WilsonOriginalObservedRoseBornChiralPurse

/-! The measured chiral inverse uses this same reflected profile on both
the finite connected energy matrix and its first filed response. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralCells
open Function Set Finset Filter MeasureTheory WithLp Lattice Wilson Maxwell
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open Table.Pairing WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonMaxwellThermometerReflectedIncidence WilsonMaxwellThermometerLowerPointGram
open WilsonMaxwellThermometerReflectedFirstPrice
open WilsonPositionProgramReflectedPurse (shape)
open scoped Classical Topology BigOperators

variable {G:Gauge}(a:Axis)(x:E4)(B:Bulb (site x) a){Q:Fin 2→SealR G}(φ:Wilt Q)
variable (received:∀i,(φ i).ψ.val=shape a x B i)

def test (t:Points 2):ℝ:=∏i,(φ i).ψ.val (fun e=>t i e)

include received in
theorem located (t:Points 2):
    test φ t=mass a x B (pairIso a (n:=1) (m:=1) t):=by
  have first:shape a x B 0 (fun e=>t 0 e)=B.r (earlier a (n:=1) (m:=1) t):=by
    apply congr_arg B.r
    apply PiLp.ext
    intro k
    fin_cases k
    rfl
  have second:shape a x B 1 (fun e=>t 1 e)=B.r (after (n:=1) (m:=1) t):=by
    apply congr_arg B.r
    apply PiLp.ext
    intro k
    fin_cases k
    rfl
  change (∏i:Fin 2,(φ i).ψ.val (fun e=>t i e))=_
  rw [Fin.prod_univ_two,received 0,received 1,first,second]
  rfl

include received in
theorem hearing (f:Pair→ℂ):
    (∫y:Pair,mass a x B y • f y)=
      ∫t:Points 2,test φ t • f (pairIso a (n:=1) (m:=1) t):=by
  have transfer:=(volume_split (n:=1) (m:=1) a).integral_comp
    (pairIso a).toHomeomorph.measurableEmbedding (fun y:Pair=>mass a x B y • f y)
  simpa only [located a x B φ received] using transfer.symm

include received in
theorem gram (W:Initialize G)(V:Normalize.Store G)(M:Mesh)(c:Four ℝ)(i:WilsonMaxwellThermometerLowerGramPrice.Index G a x)(s:Bool):
    Gram a x W V B M c i s=∫t:Points 2,test φ t •
      atPair a x W V M c i s (pairIso a (n:=1) (m:=1) t):=
  hearing a x B φ received _

include received in
theorem original (W:Initialize G)(V:Normalize.Store G)(b:Sec G 6)(M:Mesh)(c:Four ℝ)(s:Bool):
    filed a x W V B b M c s=∫t:Points 2,test φ t •
      placed a W V b s M c (pairIso a (n:=1) (m:=1) t):=
  hearing a x B φ received _
end YM.Integration.WilsonOriginalObservedRoseBornChiralCells
