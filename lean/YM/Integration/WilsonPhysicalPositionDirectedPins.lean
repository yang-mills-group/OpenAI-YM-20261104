import YM.Integration.WilsonPhysicalPositionOriginalCorners
import YM.Integration.WilsonPhysicalPositionUnturnedCut
import YM.Integration.WilsonPhysicalPositionDirectedReturn

/-! The directed branch assay uses the full original numerator. At its first
marked site the booked field is on the outer ruler and at its other site the
booked field is on the inner ruler. Every signed-axis term uses the same sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDirectedPins
open Filter Function Set Finset Lattice Wilson RG Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Orbits Maxwell MS Trace.Target Trace Trace.Pilot Extra PhysMS PhysMS.Frame XSpace XSpace.Normalize
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalPositionReflectedReturn (ports sites)
open WilsonOriginalPublicRelativeGramAddresses (shape)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S){ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
    {D T:ℕ}(k:Fin (D+1))(r t:ℝ)

def ruler (r t:ℝ)(i:Fin 2):ℝ:=if i=0 then r else t*r

def direction (v:(Bel R.family.book).Field k.val)(s:Signed)(i:Fin 2):(Bel R.family.book).Field k.val:=
  if i=0 then Pert.Scale.gear R.family.labels k.val t (ports (C:=R.family) v s i) else ports (C:=R.family) v s i

variable (B:(i:Fin 2)→Book F (l:=ℓ) H arch D T (ruler r t i))
    (v:(Bel R.family.book).Field k.val)(avoid:Finset E4)(j:ℕ)

def source (s:Signed)(z:ℕ×ℕ)(i:Fin 2):R.family.label k.val:=
  (((B i).rows k).arm true (J (ruler r t i) k.val (direction (R:=R) k t v s i))).source z

def cutoff (z:ℕ×ℕ):ℝ:=
  ∑s:Signed,(WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) (fun _:Fin 2=>k.val) j
    (WilsonOriginalPublicRelativeGramAddresses.ports R avoid sites j (t*r)) z.1 z.2
    (source F J k r t B v s z)).re

theorem unconditioned (N per:ℕ)(live:j≤N):
  cutoff F J k r t B v avoid j (N,per)=∑s:Signed,(R.family.omega N per
    (WilsonMeasuredPublicEntranceCellWords.physical R (fun _:Fin 2=>k.val) (N:=N)
      (source F J k r t B v s (N,per)) (fun _=>(1,false)) (fun i=>wrap (R.family.side j per)
        (WilsonOriginalPublicRelativeGramAddresses.ports R avoid sites j (t*r) i)) (Stock.final (Fin 2)))).re:=by
  unfold cutoff
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg Complex.re (WilsonPhysicalPositionUnturnedCut.original R _ _ _ _ _ live _).symm

theorem original (simple:G.Simple)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(positive:0<t*r):
  Tendsto (cutoff F J k r t B v avoid j) (ℓ:Filter (ℕ×ℕ))
    (𝓝 (∑s:Signed,(WilsonPhysicalPositionMixedRead.value F J (fun i:Fin 2=>decide (i=0)) (ports (C:=R.family) v s)
      (shape avoid sites (R.family.S.a j/(t*r))) r t).re)):=by
  classical
  unfold cutoff
  apply tendsto_finsetSum
  intro s _
  apply Complex.continuous_re.continuousAt.tendsto.comp
  let x (i:Fin 2) (_:Bool):S.Field k.val:=J (ruler r t i) k.val (direction (R:=R) k t v s i)
  let o:=WilsonOriginalPublicRelativeGramAddresses.ports R avoid sites j (t*r)
  have h:= (WilsonMeasuredPublicEntranceMarkedNode.original R F B (fun _:Fin 2=>k) x
    simple below j o (generic_conf 2 (WilsonOriginalPublicRelativeGramAddresses.screened R avoid sites j positive))
    (fun _=>true) (fun _=>false)).2
  have fields:(fun i:Fin 2=>J (ruler r t i) k.val (direction (R:=R) k t v s i))=
      fun i:Fin 2=>if decide (i=0) then J r k.val (Pert.Scale.gear R.family.labels k.val t (ports (C:=R.family) v s i))
        else J (t*r) k.val (ports (C:=R.family) v s i):=by
    funext i
    by_cases e:i=0 <;> simp [ruler,direction,e]
  unfold WilsonPhysicalPositionMixedRead.value
  rw [←WilsonOriginalPublicRelativeGramAddresses.placed R avoid sites j positive,←fields]
  exact h

end YM.Integration.WilsonPhysicalPositionDirectedPins
end
