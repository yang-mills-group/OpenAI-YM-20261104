import YM.Integration.WilsonOriginalPublicTrialPhaseFiling
import YM.Integration.WilsonOriginalPublicTrialPhaseTurn

/-! The joint K birth uses the exact roots and signed hard inventories of its chosen one-source grants. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCoFiled
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

open WilsonOriginalPublicTrialPhaseFiling (copy whereAt reserve)
open RG05Readout.Address (Three)

def copies {n:Side}(R₀:Rep G n)(key:V)(s:V→Motion)(off:V→Site n)(π:∀i,R₀.activities.Moves (s i).1 (off i))
    (B:I→Three G n)(i:V×I):Three G n:=
  if i.1=key then B i.2 else RG05Readout.View.spin (s i.1) (π i.1) (B i.2)


/-- The compensated originals and all their actual issued hard moves are chosen before the gas. -/
theorem original (live:K≤N)
    (d:I→ℕ)(home:I→Site ((C).side K per))(v:∀j,(C).label (d j))
    (q:∀j,Coefficient ((C).labels.level (d j)) ((C).side K per))
    (writes:∀j U,(q j).density (home j) ((C).localSection (d j)) (P) U=
      ((P).eval U:ℂ)*WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N per K (home j) (v j) U)
    (dom₀:∀j,Dominated (q j).forced)(ψ:I→MergeProof.Response G ((C).side K per))
    (won:∀j,Attainment (P).p (home j) (ψ j) (reserve R (N:=N) (d j) (home j) (v j)))
    (hook:∀j,profile (P).activities (q j).forced=MergeProof.hook (P).activities (P).p.threshold (ψ j))
    (key:V)(turn:V→Motion)(offset:V→Site ((C).side K per))
    (moves:∀i,(P).activities.Moves (turn i).1 (offset i))
    {load:ℕ} (occ:Occupancy (whereAt key turn offset home) load) (w:I→ℝ)(wpos:∀j,0<w j)
    {τ:ℝ} (budget:∀j,w j*reserve R (N:=N) (d j) (home j) (v j)≤τ)
    (tpos:0≤τ) (ex:0≤(P).p.supportExponent-3)
    (bound:(((P).p.B+(P).p.B+1:ℕ):ℝ)^4*((A).clock.forcedAllowance K+load*siteFactor (P).p.B*τ)≤3)
    (cap:Real.exp ((A).clock.forcedAllowance K+load*siteFactor (P).p.B*τ)-1≤1) :
    let raw:=fun j=>WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N per K (home j) (v j)
    let F:=copy key turn offset raw stepUp
    let o:=whereAt key turn offset home
    let flip:=fun i:V=>Equiv.swap key i
    let B:=fun i=>RG05Readout.Address.invoice (q i) (home i) ((C).localSection (d i)) (P)
    let I₀:=copies (P) key turn offset moves B
    (∀i U,(I₀ i).1 U=((P).eval U:ℂ)*F i U) ∧
      (∀i,Dominated (I₀ i).2.2) ∧
      (∀i U,(I₀ i).1 U=coin (P) (I₀ i).2.1 (I₀ i).2.2 U) ∧
      Serves (P) (fun i=>(I₀ i).2.1) (fun i=>profile (P).activities (I₀ i).2.2)
        (birth (Names V I) (P) F) key turn offset flip o (fun i=>w i.2) ((P).p.supportExponent-3) 1:=by
  intro raw F o flip B I₀
  let base:=fun j=>(q j).exponentialEntry (home j) ((C).localSection (d j)) (P)
  let f:=copy key turn offset base stepUp
  let k (i:V×I):ℕ→ Config G ((C).side K per)→ℂ:=if i.1=key then (q i.2).forced
    else fun t=>stepUp (turn i.1) (offset i.1) ((q i.2).forced ((moves i.1).kp.symm t))
  let roots (i:V×I):MergeProof.Response G ((C).side K per):=if i.1=key then ψ i.2 else upwards (turn i.1) (offset i.1) (ψ i.2)
  have dom(i:V×I):Dominated (k i):=by
    unfold k; split
    · exact dom₀ _
    · exact conduits _ _ _ (dom₀ _) (moves _)
  have routed (i:V)(h:i≠key)(j:I) :
      profile (P).activities (k (i,j))=floatUp (turn i) (offset i) (profile (P).activities (q j).forced):=by
    apply roam _ _ (moves i);intro a U;simp [k,h]
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
  have reg(i:V×I):(I₀ i).2.1=f i:=by
    rcases i with ⟨i,j⟩
    by_cases h:i=key <;> simp only [I₀,copies,f,copy,h,if_true,if_false,B,RG05Readout.Address.invoice,base,RG05Readout.View.spin]
  have owners(i:V×I):(I₀ i).2.2=k i:=by
    rcases i with ⟨i,j⟩
    by_cases h:i=key <;> simp only [I₀,copies,k,h,if_true,if_false,B,RG05Readout.Address.invoice,RG05Readout.View.spin]
  have head(i:V×I)(U):(I₀ i).1 U=((P).eval U:ℂ)*F i U:=by
    rcases i with ⟨i,j⟩
    by_cases h:i=key
    · simpa only [I₀,copies,h,if_true,B,RG05Readout.Address.invoice,F,copy] using writes j U
    · simp only [I₀,copies,h,if_false,B,RG05Readout.Address.invoice,RG05Readout.View.spin,F,copy,stepUp,writes,scalar_mul,Motion.scalar_real]
      rw [@WardBin.Wheels.rep_spins G K per N (H) (turn i).1 R.makes.wilson live U (offset i)]
  refine ⟨head,fun i=>by rw [owners];exact dom i,fun i U=>?_,?_⟩
  · rw [head,reg,owners]
    exact actual i U
  simp_rw [reg,owners]
  apply spawn (R:=(P)) (R.makes.wilson.represents N per K live).good.labels roots
    (cloth tally (fun i=>budget i.2) (fun i=>(wpos i.2).le)) (by intro i hi j;simp [roots,hi])
    (fun i _=>Equiv.swap_apply_left key i) (fun i=>⟨moves i⟩) occ tpos (fun i=>wpos i.2) le_rfl ex
    (bound.trans_eq (by ring)) cap (fun U=>(Tour.bright (H) R.makes.wilson N per K live U).ne') zero_le_one dom _ actual
  rintro ⟨i,j⟩;by_cases h:i=key
  · simpa only [roots,k,if_pos h] using (hook j).symm
  · simp only [roots,if_neg h];rw [hooked (R:=(P)) _ _ (moves i),routed i h j,hook j]


end YM.Integration.WilsonOriginalPublicTrialPhaseCoFiled
end
