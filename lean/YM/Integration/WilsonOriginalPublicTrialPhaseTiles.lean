import YM.Integration.WilsonOriginalPublicTrialPhaseFiling

/-! The physical replicated upper dose has bounded occupancy on every torus,
including sites on a reflection seam. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTiles
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon
open Push Local Marker Motion PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi OPE.Therm
open WilsonOriginalPublicTrialPhaseFiling
open scoped Classical BigOperators Topology
variable {n:Side} {G:Gauge} {I:Type} [Fintype I] [DecidableEq I]
private theorem distinct (T : Tiling n) (o : Site n) :
    Injective (fun c : T.Cell=>(T.omega c,T.copyMap c o)) := by
  intro i j h
  have s : T.omega i=T.omega j := congrArg Prod.fst h
  have e : T.copyMap i o=T.copyMap j o := congrArg Prod.snd h
  have b : T.bias i=T.bias j := by unfold Tiling.bias;rw [s]
  change (T.omega i).act o+(T.base+T.units.root i-(T.omega i).act T.base+T.bias i)=
    (T.omega j).act o+(T.base+T.units.root j-(T.omega j).act T.base+T.bias j) at e
  rw [s,b] at e
  have eq : T.base+T.units.root i=T.base+T.units.root j := sub_left_inj.mp (add_right_cancel (add_left_cancel e))
  exact T.units.embed_injective (add_left_cancel eq)

def motion (T:Tiling n)(i:T.Cell):Motion:=⟨T.omega i,decide (T.hand i)⟩

omit [Fintype I] [DecidableEq I] in
theorem picture (T:Tiling n)(q:I→ Config G n→ℂ)(i:T.Cell×I):
    copy 0 (motion T) T.translateBy q stepUp i=T.copy i.1 (q i.2):=by
  rcases i with ⟨i,j⟩
  by_cases root:i=0
  · subst i;funext U;simp [copy,T.copy_zero]
  · funext U;by_cases rev:T.hand i <;> simp [copy,root,motion,stepUp,Motion.scalar,Tiling.copy,rev]

omit [Fintype I] [DecidableEq I] in
theorem pin (T:Tiling n)(z:I→Site n)(i:T.Cell×I):
    whereAt 0 (motion T) T.translateBy z i=T.copyMap i.1 (z i.2):=by
  rcases i with ⟨i,j⟩;by_cases root:i=0
  · subst i;simp [whereAt,Tiling.copyMap,T.omega_zero,T.transport_zero,affine]
  · simp [whereAt,root,motion,Tiling.copyMap]

theorem seats (T:Tiling n)(z:I→Site n):
    Occupancy (fun i:T.Cell×I=>T.copyMap i.1 (z i.2)) (Fintype.card I*Fintype.card Signed):=by
  intro x
  let carrier:Finset (T.Cell×I):=univ.filter fun i=>T.copyMap i.1 (z i.2)=x
  let code:=fun i:T.Cell×I=>(i.2,T.omega i.1)
  have inj:Set.InjOn code (carrier:Set (T.Cell×I)):=by
    rintro ⟨i,j⟩ hi ⟨u,v⟩ hu eq
    have axis:j=v:=congrArg Prod.fst eq
    subst v
    have eqsites:T.copyMap i (z j)=T.copyMap u (z j):=
      (mem_filter.mp hi).2.trans (mem_filter.mp hu).2.symm
    have cells:i=u:=distinct T (z j) (Prod.ext (congrArg Prod.snd eq) eqsites)
    subst u;rfl
  change carrier.card≤_
  rw [←card_image_of_injOn inj]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_prod I Signed)

variable (R:Run G){K N per:ℕ}
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per K
theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(live:K≤N)
    (tiles:Tiling ((C).side K per))(d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))
    (small:∀j,((((C).localSection (d j)).footprint (z j)).card:ℝ)*(H).levels.clock.forcedAllowance K≤1)
    (w:I→ℝ)(wpos:∀j,0<w j){τ:ℝ} (budget:∀j,w j*reserve R (N:=N) (d j) (z j) (v j)≤τ)
    (tpos:0≤τ)(ex:0≤(P).p.supportExponent-3)
    (limits:let load:=Fintype.card I*Fintype.card Signed
      let total:=(H).levels.clock.forcedAllowance K+load*siteFactor (P).p.B*τ
      (((P).p.B+(P).p.B+1:ℕ):ℝ)^4*total≤3 ∧ Real.exp total-1≤1):
    let F:=fun i:tiles.Cell×I=>tiles.copy i.1 (WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d i.2) N per K (z i.2) (v i.2))
    let o:=fun i:tiles.Cell×I=>tiles.copyMap i.1 (z i.2)
    ∃ f:tiles.Cell×I→ Config G ((C).side K per)→ℂ,∃ k:tiles.Cell×I→ℕ→ Config G ((C).side K per)→ℂ,
      (∀i,Dominated (k i)) ∧
      (∀i U,((P).eval U:ℂ)*F i U=coin (P) (f i) (k i) U) ∧
      Serves (P) f (fun i=>profile (P).activities (k i)) (birth (Names tiles.Cell I) (P) F)
        0 (motion tiles) tiles.translateBy (fun i=>Equiv.swap 0 i) o (fun i=>w i.2) ((P).p.supportExponent-3) 1:=by
  have inc:Occupancy (whereAt 0 (motion tiles) tiles.translateBy z) (Fintype.card I*Fintype.card Signed):=by
    rw [funext (pin tiles z)];exact seats tiles z
  obtain ⟨f,k,hk,hf,posted⟩:=WilsonOriginalPublicTrialPhaseFiling.original R book live d z v small
    0 (motion tiles) tiles.translateBy inc w wpos budget tpos ex limits.1 limits.2
  exact ⟨f,k,hk,fun i U=>by simpa only [picture tiles _ i] using hf i U,
    by simpa only [funext (picture tiles _),funext (pin tiles z)] using posted⟩
end YM.Integration.WilsonOriginalPublicTrialPhaseTiles
