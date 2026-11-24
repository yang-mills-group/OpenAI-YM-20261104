import YM.Integration.WilsonOriginalPublicTrialPhaseBirth
import YM.Integration.WilsonOriginalNamedSlotIncome
import YM.OPE.Replicas.Lichen

/-! Simultaneous primitive births at a genuine interior Wilson date. The
reflected copies use the same attained hard records, reindexed by their true
action on the original inherited vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFiling
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon MergeProof.Float
open Push Local Marker Motion PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi OPE.Therm
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N K per:ℕ}
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per K
local notation "A" => (H).levels

def copy {n:Side}{X:Type}(v:V)(turn:V→Motion)(offset:V→Site n)(f:I→ Config G n→X)
    (act:Motion→Site n→(Config G n→X)→ Config G n→X)(i:V×I):Config G n→X:=
  if i.1=v then f i.2 else act (turn i.1) (offset i.1) (f i.2)
def whereAt {n:Side}(v:V)(turn:V→Motion)(offset:V→Site n)(home:I→Site n)(i:V×I):Site n:=
  if i.1=v then home i.2 else affine (turn i.1).1 (offset i.1) (home i.2)

def reserve (d:ℕ)(o:Site ((C).side K per))(v:(C).label d):ℝ:=
  reservedMass (P).p (((C).localSection d).footprint o)
    (BasisCost.price ((C).localSection d)*((C).labels.level d).coeffSize
      (WilsonPositionProgramBlockedTrialAddBack.names R d N per K v))

theorem original {T:Campaign R}(book:Campaign.Pillars R T)(live:K≤N)
    (d:I→ℕ)(home:I→Site ((C).side K per))(v:∀j,(C).label (d j))
    (small:∀j,((((C).localSection (d j)).footprint (home j)).card:ℝ)*(A).clock.forcedAllowance K≤1)
    (key:V)(turn:V→Motion)(offset:V→Site ((C).side K per))
    {load:ℕ} (occ:Occupancy (whereAt key turn offset home) load) (w:I→ℝ)(wpos:∀j,0<w j)
    {τ:ℝ} (budget:∀j,w j*reserve R (N:=N) (d j) (home j) (v j)≤τ)
    (tpos:0≤τ) (ex:0≤(P).p.supportExponent-3)
    (bound:(((P).p.B+(P).p.B+1:ℕ):ℝ)^4*((A).clock.forcedAllowance K+load*siteFactor (P).p.B*τ)≤3)
    (cap:Real.exp ((A).clock.forcedAllowance K+load*siteFactor (P).p.B*τ)-1≤1) :
    let raw:=fun j=>WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N per K (home j) (v j)
    let F:=copy key turn offset raw stepUp
    let o:=whereAt key turn offset home
    let flip:=fun i:V=>Equiv.swap key i
    ∃ f:V×I→ Config G ((C).side K per)→ℂ,∃ k:V×I→ℕ→ Config G ((C).side K per)→ℂ,
      (∀i,Dominated (k i)) ∧
      (∀i U,((P).eval U:ℂ)*F i U=coin (P) (f i) (k i) U) ∧
      Serves (P) f (fun i=>profile (P).activities (k i)) (birth (Names V I) (P) F)
        key turn offset flip o (fun i=>w i.2) ((P).p.supportExponent-3) 1:=by
  intro raw F o flip
  choose q _ fmt writes rem ψ won hook using fun j=>WilsonOriginalPublicTrialPhaseBirth.original R book live
    (d j) (home j) (v j) (small j)
  let base:=fun j=>(q j).exponentialEntry (home j) ((C).localSection (d j)) (P)
  let f:=copy key turn offset base stepUp
  let moves i:=((R.makes.wilson.represents N per K live).good.labels.moves (turn i).1 (offset i)).some
  let k (i:V×I):ℕ→ Config G ((C).side K per)→ℂ:=if i.1=key then (q i.2).forced
    else fun t=>stepUp (turn i.1) (offset i.1) ((q i.2).forced ((moves i.1).kp.symm t))
  let roots (i:V×I):MergeProof.Response G ((C).side K per):=if i.1=key then ψ i.2 else upwards (turn i.1) (offset i.1) (ψ i.2)
  have dom₀ j:Dominated (q j).forced:=rem_dominated (rem j)
  have dom(i:V×I):Dominated (k i):=by
    unfold k; split
    · exact dom₀ _
    · exact conduits _ _ _ (dom₀ _) (moves _)
  have routed (i:V)(h:i≠key)(j:I) :
      profile (P).activities (k (i,j))=floatUp (turn i) (offset i) (profile (P).activities (q j).forced):=by
    apply roam _ _ (moves i);intro a U;simp [k,h];rfl
  have tally(i:V×I):Attainment (P).p (o i) (roots i) (reserve R (N:=N) (d i.2) (home i.2) (v i.2)):=by
    rcases i with ⟨i,j⟩; by_cases h:i=key
    · simpa only [o,whereAt,roots,reserve,if_pos h] using won j
    · simpa only [o,whereAt,roots,reserve,if_neg h] using rise (turn i) (offset i) (won j)
  have plain(j:I)(U):((P).eval U:ℂ)*raw j U=coin (P) (base j) (q j).forced U:=by
    dsimp only [base]
    rw [coin_primary]
    exact (writes j U).symm
  have actual(i:V×I)(U):((P).eval U:ℂ)*F i U=coin (P) (f i) (k i) U:=by
    rcases i with ⟨i,j⟩; by_cases h:i=key
    · simpa only [F,f,copy,k,if_pos h] using plain j U
    · have eq:=opals (turn i) (H) R.makes.wilson live (offset i) (base j) (moves i) (dom₀ j)
          (dom (i,j)) (routed i h j)
      simp only [F,f,copy,if_neg h]
      rw [eq]
      simp only [stepUp,← plain j,scalar_mul,Motion.scalar_real]
      rw [@WardBin.Wheels.rep_spins G K per N (H) (turn i).1 R.makes.wilson live U (offset i)]
  refine ⟨f,k,dom,actual,?_⟩
  apply spawn (R:=(P)) (R.makes.wilson.represents N per K live).good.labels roots
    (cloth tally (fun i=>budget i.2) (fun i=>(wpos i.2).le)) (by intro i hi j;simp [roots,hi])
    (fun i _=>Equiv.swap_apply_left key i) (fun i=>⟨moves i⟩) occ tpos (fun i=>wpos i.2) le_rfl ex
    (bound.trans_eq (by ring)) cap (fun U=>(Tour.bright (H) R.makes.wilson N per K live U).ne') zero_le_one dom _ actual
  rintro ⟨i,j⟩;by_cases h:i=key
  · simpa only [roots,k,if_pos h] using (hook j).symm
  · simp only [roots,if_neg h];rw [hooked (R:=(P)) _ _ (moves i),routed i h j,hook j]

end YM.Integration.WilsonOriginalPublicTrialPhaseFiling
