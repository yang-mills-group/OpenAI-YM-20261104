import YM.Integration.WilsonPhysicalPositionGridReturn
import YM.Integration.WilsonOriginalPublicRelativeGramAddresses
import YM.Integration.WilsonMeasuredPublicEntranceMarkedNode

/-! The original N-born four measurements for the bounded-ratio branch detector use the same two sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionOriginalCorners
open Filter Function Set Finset Lattice RG Wilson Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Orbits Maxwell MS Trace.Target Trace Trace.Pilot Extra PhysMS PhysMS.Frame XSpace XSpace.Normalize
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonMeasuredPublicEntranceMarkedNode (field)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonPhysicalPositionTwoHomeObservable (heard)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (J:ℝ→tower S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  {n d cap T:ℕ}(height:d≤cap)
local notation "D₀" => (Bel R.family.book).Field
local notation "ds" => (fun _:Fin n=>d)

def sign (useSmall:Bool):ℂ:=if useSmall then -1 else 1
def home (r t:ℝ)(useSmall:Bool):ℝ:=if useSmall then t*r else r
def inputs (p:Fin n→D₀ d)(t:ℝ)(useSmall:Fin n→Bool)(i:Fin n):D₀ d:=
  if useSmall i then p i else Pert.Scale.gear R.family.labels d t (p i)

def incumbent (p:Fin n→D₀ d)(r t:ℝ)(b:Fin n→Bool)(i:Fin n):S.Field d:=
  J (home r t (b i)) d (inputs R p t b i)

theorem expanded (x:Points n)(p:Fin n→D₀ d)(r t:ℝ):
    heard F J p x r t=∑b:Fin n→Bool,(∏i,sign (b i))*
      S.classMoment S ds ((t*r) • x) (incumbent R J p r t b):=by
  classical
  let M:=S.classMoment S ds ((t*r) • x)
  let w (i:Fin n)(k:Bool):S.Field d:=if k then J (t*r) d (p i) else J r d (Pert.Scale.gear R.family.labels d t (p i))
  have arg:(fun i=>J r d (Pert.Scale.gear R.family.labels d t (p i))-J (t*r) d (p i))=
      fun i=>∑k:Bool,sign k • w i k:=by
    funext i
    rw [Fintype.sum_bool]
    change _=(-1:ℂ) • J (t*r) d (p i) + (1:ℂ) • J r d (Pert.Scale.gear R.family.labels d t (p i))
    rw [neg_one_smul,one_smul,sub_eq_add_neg,add_comm]
  change M _=_
  rw [arg,MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro b _
  have both:(fun i=>w i (b i))=incumbent R J p r t b:=by
    funext i
    cases q:b i <;> simp [w,incumbent,home,inputs,q]
  exact (M.map_smul_univ (fun i=>sign (b i)) (fun i=>w i (b i))).trans (by rw [both];rfl)

variable (p:Fin n→(Bel R.family.book).Field d)(r t:ℝ)(books:(b:Bool)→Book F (l:=l) H arch cap T (home r t b))
  (avoid:Finset E4)(x:Points n)(j:ℕ)

theorem original (simple:G.Simple)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(positive:0<t*r):
    Tendsto (fun z:ℕ×ℕ=>∑b:Fin n→Bool,(∏i,sign (b i))*(WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) ds j
        (WilsonOriginalPublicRelativeGramAddresses.ports R avoid x j (t*r)) z.1 z.2
        (WilsonMeasuredPublicEntranceMarkedNode.field R F (fun i=>books (b i)) (fun _:Fin n=>(⟨d,Nat.lt_succ_of_le height⟩:Fin (cap+1)))
          (fun i _=>incumbent R J p r t b i) (fun _=>true) (fun _=>false) z)))
      (l:Filter (ℕ×ℕ)) (𝓝 (heard F J p (shape avoid x (R.family.S.a j/(t*r))) r t)):=by
  rw [expanded R F J,←WilsonOriginalPublicRelativeGramAddresses.placed R avoid x j positive]
  apply tendsto_finsetSum
  intro b _
  apply Tendsto.const_mul
  have paid:=WilsonMeasuredPublicEntranceMarkedNode.original R F (fun i=>books (b i)) (fun _:Fin n=>(⟨d,Nat.lt_succ_of_le height⟩:Fin (cap+1)))
    (fun i _=>incumbent R J p r t b i) simple below j (ports R avoid x j (t*r))
    (generic_conf n (WilsonOriginalPublicRelativeGramAddresses.screened R avoid x j positive)) (fun _=>true) (fun _=>false)
  exact paid.2

end YM.Integration.WilsonPhysicalPositionOriginalCorners
end
