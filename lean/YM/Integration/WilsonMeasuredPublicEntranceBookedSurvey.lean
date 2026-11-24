import YM.Integration.WilsonMeasuredPublicEntranceBookedStencil
import YM.Integration.WilsonMovingForkProfileSamples
import YM.Integration.WilsonMeasuredPublicEntranceOrderedHearing

/-! A joint signed test on all occupied original weak and pooled choices.
The measured interpolation rows are common to these choices and to their
reflected halves. Their total variation is paid independently of the radius. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonMeasuredPublicEntranceBookedSurvey
open Function Filter Set Finset Metric Lattice Wilson RG Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open FVA2.O
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridTree WilsonSeparatedGridDesign WilsonSeparatedBranchStencil
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17 PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonMeasuredPublicEntranceBookedStencil (date chart)
open WilsonMeasuredPublicEntranceOrderedHearing (sum_bound)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{E:Type}[Fintype E]{n:ℕ}
structure Press (R:Run G)(φ:Test n)(r:ℝ)(rp:0<r)(j m:ℕ)(ref:E→E4) where
  Entry:Type
  count:Fintype Entry
  centre:Entry→tsupport φ
  coeff:Entry→ℂ
  port:(k:Entry)→(sold m ref (div_pos (R.family.S.a_pos j) rp) (centre k).val).sample→Fin n→ Cover
attribute [instance] Press.count
variable {φ:Test n}{r:ℝ}{rp:0<r}{j m:ℕ}{ref:E→E4}
def model (A:Press R φ r rp j m ref)(i:A.Entry):Trial n:=
  sold m ref (div_pos (R.family.S.a_pos j) rp) (A.centre i).val

def reading (A:Press R φ r rp j m ref)(X:Points n→ℂ):ℂ:=
  ∑i,A.coeff i*read (model A i) X

def live (A:Press R φ r rp j m ref):Prop:=
  ∀i,∀q:(model A i).sample,tag (R.family.S.a j) (A.port i q)=r • (model A i).site q ∧
    tag (R.family.S.a j) (A.port i q)∈generic n ∧ tag (R.family.S.a j) (A.port i q)∈conf n

def owned (A:Press R φ r rp j m ref)(M η:ℝ):Prop:=∀i,∀q:(model A i).sample,
  (∀a,‖R.family.S.gridPoint j (A.port i q a)‖≤(M+1)*r) ∧
    Pairwise fun a b=>(η/2)*r≤‖R.family.S.gridPoint j (A.port i q a)-R.family.S.gridPoint j (A.port i q b)‖

theorem price (A:Press R φ r rp j m ref){V:ℝ}(paid:∑i,‖A.coeff i‖≤V):
    ∑i,‖A.coeff i‖*bill (model A i)≤V*(total n m E)^levels n:=by
  calc
    _≤∑i,‖A.coeff i‖*((total n m E)^levels n):=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left
      (checked m ref (div_pos (R.family.S.a_pos j) rp) (A.centre i).val).2.1 (norm_nonneg _)
    _≤_:=by rw [←sum_mul];exact mul_le_mul_of_nonneg_right paid (pow_nonneg (total_nonneg ..) _)

variable {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    (J:ℝ→tower S)(Z:WilsonPrescription G)
    {I:Type}[Fintype I][Nonempty I]{D T:ℕ}(d:I→Fin (D+1)){δ:ℝ}
    (books:(r:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T r.val)
local notation "g" => wilson z

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:Trace.Terrace.PostT R.family.path.levels)
    (slow:WilsonWindowReportingPace.Slow R.kit)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)(pick:Fin n→I)(ref:E→E4)
    (φ:Test n){η M:ℝ}(ep:0<η)(bound:∀X∈tsupport φ,∀i,‖X i‖≤M)
    (apart:∀X∈tsupport φ,∀i k,i≠k→η≤dist (X i) (X k))(P:ℕ):
    ∃m:ℕ,∃K:ℝ,0≤K ∧ ∀ᶠt in trail,∀r:{s:ℝ // 0<s ∧ s<δ},r.val=t → Housed F (books r) →
      ∀y:(i:I)→(Bel R.family.book).Field (d i).val,∀v:(i:I)→Free R.family (d i).val,∀marked:Fin n→Bool,
      let field:=fun b=>chart F J Z d books pick r y v b marked
      ∃A:Press R φ r.val r.property.1 (date (I:=I) F books r) m ref,
        live A ∧ owned A M η ∧ ∑i,‖A.coeff i‖≤Read.Value φ+1 ∧
        ∀α:(Fin n→Bool)→ℂ,‖(∑b,α b*φ.applyTo (field b))-∑b,α b*reading A (field b)‖≤
          (∑b,‖α b‖)*(1+(Read.Value φ+1)*K*(∏i,(‖v (pick i)‖+‖y (pick i)‖)))*(g r.val)^P:=by
  classical
  obtain ⟨m,K,kn,sale⟩:=WilsonMeasuredPublicEntranceBookedStencil.original F J Z d books simple bliss cash slow below lead owed pick E (M:=M) ep P
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  refine ⟨m,K,kn,?_⟩
  filter_upwards [sale,link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r ready gp g1
  intro s eq house y v marked field
  subst r
  let Q:=(g s.val)^P
  have qp:0<Q:=pow_pos gp _
  have q1:Q≤1:=pow_le_one₀ gp.le g1
  have smooth(b:Fin n→Bool):ContinuousOn (field b) (tsupport φ):=by
    have good:= (S.class_smooth S F.room.kernel.smooth (fun i:Fin n=>(⟨(d (pick i)).val,
      WilsonMeasuredPublicEntranceWeakTestCost.slot F (marked i) (WilsonOriginalTwoFlatPublicNamedFare.chosen F J Z s.val
        ((books s).V (d (pick i))) (b i) (y (pick i)) (v (pick i)))⟩:S.Tag))).continuousOn
    exact good.comp (continuous_const_smul s.val).continuousOn (fun _ h=>Work.A05.smul_conf s.property.1 (φ.tsupport_subset h))
  obtain ⟨ι,fi,x,μ,spent,fits⟩:=WilsonMovingForkProfileSamples.one φ field smooth qp
  letI:=fi
  let f₀:=date (I:=I) F books s
  let dp:=div_pos (R.family.S.a_pos f₀) s.property.1
  have actual:=fun i=>ready s rfl house ref (x i).val (bound _ (x i).property) (apart _ (x i).property)
  choose port incident using fun i q=>(actual i).1 q
  let A:Press R φ s.val s.property.1 f₀ m ref:=⟨ι,fi,x,μ,port⟩
  have totalμ:∑i,‖μ i‖≤Read.Value φ+1:=spent.trans (add_le_add le_rfl q1)
  refine ⟨A,fun i q=>⟨(incident i q).1,(incident i q).2.1,(incident i q).2.2.1⟩,
      fun i q=>(incident i q).2.2.2,totalμ,?_⟩
  let H₀:=∏i,(‖v (pick i)‖+‖y (pick i)‖)
  have hn:0≤H₀:=prod_nonneg fun _ _=>add_nonneg (norm_nonneg _) (norm_nonneg _)
  have each(b:Fin n→Bool):‖φ.applyTo (field b)-reading A (field b)‖≤(1+(Read.Value φ+1)*K*H₀)*Q:=by
    have row:=sum_bound (s:=univ) (μ:=μ) (A:=fun i=>field b (x i)) (B:=fun i=>read (model A i) (field b))
      (fun i _=>(actual i).2 y v b marked)
    calc
      _≤‖φ.applyTo (field b)-∑i,μ i*field b (x i)‖+
          ‖(∑i,μ i*field b (x i))-reading A (field b)‖:=norm_sub_le_norm_sub_add_norm_sub ..
      _≤Q+(∑i,‖μ i‖)*(K*H₀*Q):=add_le_add (fits b) row
      _≤Q+(Read.Value φ+1)*(K*H₀*Q):=by gcongr
      _= _:=by ring
  intro α
  exact (sum_bound (s:=univ) (μ:=α) (fun b _=>each b)).trans_eq (by ring)

end YM.Integration.WilsonMeasuredPublicEntranceBookedSurvey
end
