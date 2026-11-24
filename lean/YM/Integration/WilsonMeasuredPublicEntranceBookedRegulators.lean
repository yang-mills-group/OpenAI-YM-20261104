import YM.Integration.WilsonMeasuredPublicEntranceBookedSurvey
import YM.Integration.WilsonMeasuredPublicEntranceMarkedNode

/-! Pass the two original regulators on the fixed printed rows. A source
which varies over cutoffs keeps its actual projection up to the elected
limit where the source approaches its filed label. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
namespace YM.Integration.WilsonMeasuredPublicEntranceBookedRegulators
open Function Filter Set Finset Metric Lattice Wilson RG Extraction Table Spec PhysMS Climb
open FVA2 FVA2.O FVA2.Register MS MS.Land RG17 PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceBookedSurvey (Press model live reading)
open WilsonMeasuredPublicEntranceWeakTestCost (slot)
open WilsonMeasuredPublicEntranceMarkedNode (field)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open WilsonSeparatedBranchStencil
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T n:ℕ}{ρ:Fin n→ℝ}(B:∀i,Book F (l:=l) H z D T (ρ i))
    (d:Fin n→Fin (D+1))(v:∀i,Bool→S.Field (d i).val)
    {E:Type}[Fintype E]{φ:Test n}{r:ℝ}{rp:0<r}{j m:ℕ}{ref:E→E4}
    (A:Press R φ r rp j m ref)
local notation "ds" => (fun i:Fin n=>(d i).val)


def collect (Q:(i:A.Entry)→(model A i).sample→ℂ):ℂ:=
  ∑i,A.coeff i*(letI:=(model A i).count; ∑a:(model A i).sample,(model A i).weight a • Q i a)

def batch (α:(Fin n→Bool)→ℂ)(marked:Fin n→Bool)(w:ℕ×ℕ):ℂ:=
  ∑b,α b*collect A (fun i a=>physical (C:=R.family) ds j (A.port i a) w.1 w.2 (field R F B d v b marked w))

def moving (α:(Fin n→Bool)→ℂ)(marked:Fin n→Bool)(w:ℕ×ℕ):ℂ:=
  ∑b,α b*collect A (fun i a=>publicValue (S:=S) ds j (A.port i a) (field R F B d v b marked w))

def target (α:(Fin n→Bool)→ℂ)(marked:Fin n→Bool):ℂ:=
  ∑b,α b*reading A (fun X=>S.classMoment S ds (r • X) (fun k=>slot F (marked k) (v k (b k))))

private theorem sum_limit {L:Type}{u:Filter L}{Q:L→(i:A.Entry)→(model A i).sample→ℂ}
    {q:(i:A.Entry)→(model A i).sample→ℂ}(each:∀i a,Tendsto (fun w=>Q w i a) u (𝓝 (q i a))):
    Tendsto (fun w=>collect A (Q w)) u (𝓝 (collect A q)):=by
  classical
  unfold collect
  apply tendsto_finsetSum
  intro i _
  apply Tendsto.const_mul
  letI:=(model A i).count
  exact tendsto_finsetSum _ fun a _=>(each i a).const_smul _

theorem original (simple:G.Simple)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(valid:live A)
    (α:(Fin n→Bool)→ℂ)(marked:Fin n→Bool):
    Tendsto (fun w=>batch F B d v A α marked w-moving F B d v A α marked w) f.fuse (𝓝 0) ∧
      Tendsto (batch F B d v A α marked) (l:Filter (ℕ×ℕ)) (𝓝 (target F d v A α marked)):=by
  classical
  let P:=fun b (w:ℕ×ℕ) (i:A.Entry) (a:(model A i).sample)=>physical (C:=R.family) ds j (A.port i a)
    w.1 w.2 (field R F B d v b marked w)
  let Q:=fun b w (i:A.Entry) (a:(model A i).sample)=>publicValue (S:=S) ds j (A.port i a)
    (field R F B d v b marked w)
  let V:=fun (b:Fin n→Bool) (i:A.Entry) (a:(model A i).sample)=>S.classMoment S ds
    (r • (model A i).site a) (fun k=>slot F (marked k) (v k (b k)))
  have receipts(b:Fin n→Bool)(i:A.Entry)(a:(model A i).sample):=
    WilsonMeasuredPublicEntranceMarkedNode.original R F B d v simple below j (A.port i a) (valid i a).2.2 b marked
  have actual(b:Fin n→Bool)(i:A.Entry)(a:(model A i).sample):
      Tendsto (fun w=>P b w i a) (l:Filter (ℕ×ℕ)) (𝓝 (V b i a)):=by
    have pos:Extraction.Order.grid R.family j (A.port i a)=r • (model A i).site a:=(valid i a).1
    simpa only [P,V,pos] using (receipts b i a).2
  constructor
  · have zero(b:Fin n→Bool):Tendsto (fun w=>collect A fun i a=>P b w i a-Q b w i a) f.fuse (𝓝 0):=by
      have sampled:=sum_limit A (Q:=fun w i a=>P b w i a-Q b w i a) (q:=fun _ _=>0) (fun i a=>(receipts b i a).1)
      simpa only [collect,smul_zero,sum_const_zero,mul_zero] using sampled
    have receipt:=tendsto_finsetSum univ (fun b _=>(zero b).const_mul (α b))
    simpa only [collect,P,Q,batch,moving,smul_sub,mul_sub,Finset.sum_sub_distrib,mul_zero,sum_const_zero] using receipt
  · apply tendsto_finsetSum
    intro b _
    exact (sum_limit A (Q:=P b) (q:=V b) (actual b)).const_mul _

end YM.Integration.WilsonMeasuredPublicEntranceBookedRegulators
end
