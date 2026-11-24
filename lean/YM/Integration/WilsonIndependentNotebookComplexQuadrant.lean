import YM.Integration.WilsonIndependentConditionedBankMatrix
import YM.Integration.WilsonIndependentNotebookReflectedPoint

/-! The four signed real samples on one held clock reconstruct its complete complex row. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookComplexQuadrant
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedPivotCash (measured view gross)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open Extra.Histories
open WilsonIndependentConditionedBankMatrix (sample pivot protocol)
variable {G:Gauge}{e:ℕ}{L:Credit}

def phase (s:Motion):ℂ:=if s.2 then -Complex.I else Complex.I

theorem oriented (s:Motion):phase s=Motion.scalar s Complex.I:=by
  cases s with |mk a b=>cases b <;> simp [phase,Motion.scalar]

theorem unit (s:Motion):‖phase s‖=1:=by unfold phase; split <;> simp

def fuse (s:Motion)(x:Bool→ℂ):ℂ:=x false+phase s*x true

theorem real_fee (q:ℕ)(g:ℝ)(f:Cost):∃r:ℝ,measured q g f=(r:ℂ):=by
  refine ⟨∑j∈Finset.range (q+1),g^j*PowerSeries.coeff j f,?_⟩
  simp [measured,WilsonPhysicalMarkedDefect.RawBank.cash,embed]

theorem axes (s:Motion)(x:Bool→ℂ)(cash:∀i,∃r:ℝ,x i=(r:ℂ))(b:Bool):‖x b‖≤‖fuse s x‖:=by
  obtain ⟨u,hu⟩:=cash false
  obtain ⟨v,hv⟩:=cash true
  have hre:=Complex.abs_re_le_norm (fuse s x)
  have him:=Complex.abs_im_le_norm (fuse s x)
  cases s with
  |mk a bar=>
    cases bar <;> cases b <;> simp [fuse,phase,hu,hv,Complex.mul_re,Complex.mul_im] at hre him ⊢ <;> assumption

theorem two (s:Motion)(x y:Bool→ℂ){B:ℝ}(bound:∀i,‖x i-y i‖≤B):
    ‖fuse s x-fuse s y‖≤2*B:=by
  have eq:fuse s x-fuse s y=(x false-y false)+phase s*(x true-y true):=by unfold fuse;ring
  rw [eq]
  calc
    _≤‖x false-y false‖+‖phase s*(x true-y true)‖:=norm_add_le _ _
    _≤_:=by rw [norm_mul,unit,one_mul]; linarith [bound false,bound true]

theorem quartet (a b:Motion)(x y:Bool→Bool→ℂ){B:ℝ}(bound:∀i j,‖x i j-y i j‖≤B):
    ‖fuse a (fun i=>fuse b (x i))-fuse a (fun i=>fuse b (y i))‖≤4*B:=
  (two a _ _ (fun i=>two b _ _ (bound i))).trans_eq (by ring)

theorem tilted (R:Realm G (e+1) L)(Q:SealR G)(N m:ℕ)(a:Motion)(x:Bool→Alma Q.F→ℂ)(i:Alma Q.F):
    pivot R Q N m (fun j=>fuse a (fun c=>x c j)) i=fuse a (fun c=>pivot R Q N m (x c) i):=by
  unfold pivot fuse
  simp only [Complex.real_smul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  apply congrArg (_ + ·)
  exact sum_congr rfl (fun j _=>by ring)

theorem measured (R:Realm G (e+1) L)(Q₁ Q₂:SealR G)(k host m K N:ℕ)
    (φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(s:ℕ)(z:Fin s→YForest G)(q:ℕ)(g:ℝ)
    (θ ψ':Motion)(x:Bool→Alma Q₁.F→ℂ)(v:Bool→Alma Q₂.F→ℂ):
    protocol R Q₁ Q₂ k host m K N φ ψ y o s z q g (fun i=>fuse θ (fun c=>x c i)) (fun j=>fuse ψ' (fun c=>v c j))=
      fuse θ (fun a=>fuse ψ' (fun b=>protocol R Q₁ Q₂ k host m K N φ ψ y o s z q g (x a) (v b))):=by
  unfold protocol
  simp_rw [tilted]
  unfold fuse
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring
end YM.Integration.WilsonIndependentNotebookComplexQuadrant
