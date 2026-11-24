import YM.Integration.WilsonPhysicalPositionCutoffBranch
import YM.Integration.WilsonPhysicalPositionPairMesh

/-! The directed orientation measurement uses the genuine weak books on their
open interval and the actual common reporter of both measured fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionBookedBranch
open Filter Function Set Finset Lattice Wilson RG Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Orbits OPE.Therm Maxwell MS Trace.Target Trace Trace.Pilot Extra PhysMS PhysMS.Frame XSpace XSpace.Normalize
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalPositionDirectedPins (ruler cutoff)
open WilsonPhysicalPositionDirectedTest (baseline)
open WilsonMovingForkOpticalBook (reporter)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→tower S){ℓ:Ultrafilter (ℕ×ℕ)}
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}{δ:ℝ}
set_option quotPrecheck false
local notation "X" => (Bel R.family.book).Field
variable (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=ℓ) H arch D T s.val)

def Admitted (δ r t:ℝ):Prop:=0<r ∧ r<δ ∧ t∈Icc (1/2:ℝ) 1

def home {r t:ℝ}(h:Admitted δ r t)(i:Fin 2):{s:ℝ // 0<s ∧ s<δ}:=
  ⟨WilsonPhysicalPositionDirectedPins.ruler r t i,by
    unfold WilsonPhysicalPositionDirectedPins.ruler
    split
    · exact ⟨h.1,h.2.1⟩
    · exact ⟨mul_pos ((show (0:ℝ)<1/2 by norm_num).trans_le h.2.2.1) h.1,
        (mul_le_of_le_one_left h.1.le h.2.2.2).trans_lt h.2.1⟩⟩

def station (r t:ℝ):ℕ:=if h:Admitted δ r t then reporter F books (home h) else 0

private theorem interval {ε:ℝ}(e:0<ε):∀ᶠr in trail,0<r ∧ r<ε:=
  mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ε,e,fun _ h=>h⟩

theorem ratio (simple:G.Simple)(bliss:Bliss F ℓ arch H)(slow:WilsonWindowReportingPace.Slow R.kit)(δp:0<δ)(k:Fin (D+1)):
    ∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,0<R.family.S.a (station (δ:=δ) F books r t)/(t*r) ∧
      R.family.S.a (station (δ:=δ) F books r t)/(t*r)≤(wilson arch (t*r))^2:=by
  obtain ⟨q,hq,earned⟩:=mem_nhdsGT_iff_exists_Ioo_subset.mp
    (WilsonPhysicalPositionPairMesh.original F books simple bliss slow k)
  filter_upwards [interval (lt_min δp hq)] with r live
  intro t ht
  have h:Admitted δ r t:=⟨live.1,(lt_min_iff.mp live.2).1,ht⟩
  let inner:{s:ℝ // 0<s ∧ s<δ}:=⟨t*r,mul_pos ((show (0:ℝ)<1/2 by norm_num).trans_le ht.1) h.1,
    (mul_le_of_le_one_left h.1.le ht.2).trans_lt h.2.1⟩
  let outer:{s:ℝ // 0<s ∧ s<δ}:=⟨r,h.1,h.2.1⟩
  have eq:home h=WilsonPhysicalPositionPairMesh.two inner outer:=by
    funext i
    apply Subtype.ext
    by_cases e:i=0 <;> simp [WilsonPhysicalPositionDirectedPins.ruler,home,WilsonPhysicalPositionPairMesh.two,inner,outer,e]
  have floor:inner.val≤r:=mul_le_of_le_one_left h.1.le ht.2
  have span:r≤2*inner.val:=by
    change r≤2*(t*r)
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht.1) h.1.le]
  have term:=earned (show inner.val∈Ioo 0 q from ⟨inner.2.1,floor.trans_lt (lt_min_iff.mp live.2).2⟩)
    inner outer rfl floor span
  exact ⟨div_pos (R.family.S.a_pos _) inner.2.1,by simpa only [station,dif_pos h,eq] using term⟩

theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)(V:Store G)(k:Fin (D+1))(avoid:Finset E4):
    ∃v:X k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      ((∀ᶠr in trail,∀t,∀h:Admitted δ r t,∀ᶠ z in (ℓ:Filter (ℕ×ℕ)),
        baseline v-a≤cutoff F J k r t (fun i=>books (home h i)) v avoid (station (δ:=δ) F books r t) z)→
       ∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J k.val c):=by
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have pos:∀ᶠs in trail,0<(wilson arch s)^2:=link.positive.mono fun _ h=>pow_pos h _
  have small:Tendsto (fun s=>(wilson arch s)^2) trail (𝓝 0):=by simpa using (link.conforms simple).pow 2
  obtain ⟨v,hv,a,ha,apply⟩:=WilsonPhysicalPositionCutoffBranch.original (ℓ:=ℓ) (H:=H) (arch:=arch) (T:=T)
    F J simple below lead V k avoid (station (δ:=δ) F books) (fun s=>(wilson arch s)^2) pos small
    (ratio (δ:=δ) F books simple bliss slow δp k)
  refine ⟨v,hv,a,ha,?_⟩
  intro measured
  apply apply
  filter_upwards [interval δp,measured] with r hr bill
  intro t ht
  have h:Admitted δ r t:=⟨hr.1,hr.2,ht⟩
  exact ⟨fun i=>books (home h i),bill t h⟩

end YM.Integration.WilsonPhysicalPositionBookedBranch
end
