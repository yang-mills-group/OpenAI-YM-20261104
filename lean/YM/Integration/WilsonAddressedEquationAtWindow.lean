import YM.Integration.WilsonAddressedEquationReturn

noncomputable section
namespace YM.Integration.WilsonAddressedEquationAtWindow
open Filter Lattice Wilson Labels RG Push Source Extra.Histories Extra.Histories.Relay
open RG05Readout.Aligned MergeProof Bid WilsonAddressedEquationShelf
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {d N p:ℕ} {V:SectionData (C.labels.level d)} {W:Worth}
variable {u ψ:ℕ→ℝ} {ζ:ℕ→ℕ→ℝ} {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "L"=> C.localSection d
local notation "R!"=> C.path.rep N p

/-- File the very same transported Haar equation at its own coordinate at the weak date.
The changed file is recorded at that date in its measured coordinates. -/
theorem original (real:C.Makes) {j:(F).Index} {E:ℝ} {x:C.label d}
    (income:Issued C V N p W u ψ ζ D j E x) :
    ∃ M:Music (F) C.path N p, RG05Readout.Aligned.Committed C N p d W ψ D M ∧
    ∀ w, C.ref d≤w → w≤N →
      ∃ (y:C.label d) (field:∀ i,Coefficient (F) (C.side i p)) (fee:ℕ→ℝ),
      gainChart C.path N w*(F).coeffSize ((M.tone w).index (y-x)) ≤ E ∧
      (field w).x=0 ∧
      (∀ U,(field N).density 0 (L) ((R!) N) U =
        ((C.S.a N:ℂ)^d)*(((R!) N).eval U:ℂ)*
          (initial V C.path N p (Size.axis (F) j) 0 U - initial (L) C.path N p y 0 U)) ∧
      (∀ i : ℕ, w ≤ i → i < N →
        (field i).density 0 (L) ((R!) i)=blast C.path N p i d ((field (i+1)).density 0 (L) ((R!) (i+1)))) ∧
      ∀ i : ℕ, w ≤ i → i ≤ N →
        (field i).Format 0 C.params ((R!) i) ∧
        (field i).remBound 0 ((R!) i) (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (fee i) ∧
        gainChart C.path N i*(fee i+(F).coeffSize (field i).x) ≤ E := by
  obtain ⟨Z,t,q,_,cream,M,committee,S,track,label⟩ := income
  have identity : x=(S (C.ref d)).a := (C.factory d N p).terminal.injective label
  have top := committee.sessions.sung.earned N track.admissible le_rfl
  have born := originate (L) C.path N p C.params M (m:=N) le_rfl real.wilson top track.opens track.funds cream.charge
  refine ⟨M,committee,?_⟩
  intro w lo hi
  let y := (S w).a
  let Q := dualize C.path N p M w N S (-y)
  have key i (lower:w ≤ i) (upper:i ≤ N) z := keys (L) C.path N p C.params M z
    (track.traces.chairs i (lo.trans lower) upper) (committee.sessions.sung.earned i (lo.trans lower) upper)
  have woke : Q.Woke C.params W (L) q := by
    refine ⟨⟨hi,le_rfl⟩,fun i lower upper=>(key i lower upper _).2,?_ ,
      fun i lower upper=>(track.traces.ships i (lo.trans lower) upper).tunes _,
      fun i lower upper=>(track.traces.ships i (lo.trans lower) upper).debt _,?_,?_⟩
    · intro i _ _
      let a := (C.path.levels.clock.op i p).ratio
      change 0=a.parent 0
      have atRoot := a.embed_parent 0
      rw [Motion.embed_origin] at atRoot
      exact atRoot.symm
    · change ((S w).bar M (-y)).x=0
      rw [(key w le_rfl hi _).1]
      simp [y]
    change (S N).cost M _ ≤ _
    simp_rw [show Q.voice N=(S N).bar M (-y) from rfl,track.starts]
    exact (born.2 _).2.2
  have wallet := Work.G09.answer W C.path committee.sessions.credit committee.sessions.brine N p d w N
    (F) (L) C.params Q q cream.fuel.le woke
  refine ⟨y,Q.voice,Q.cost,?_,woke.pairing,?_,fun i lower upper=>track.transfer i (lo.trans lower) upper (-y),?_⟩
  · have original := track.expenses w lo hi
    have held := key w le_rfl hi (-x)
    rw [←identity] at original
    change gainChart C.path N w*((S w).cost M (-x)+(F).coeffSize ((S w).bar M (-x)).x) ≤ _ at original
    rw [held.1] at original
    have nonneg := rem_nonneg held.2.2
    rw [sub_eq_add_neg]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left nonneg) (Real.exp_pos _).le).trans (original.trans cream.dom)
  · intro U
    have encode := (real.calibrated d N p track.admissible).encode (-y) U
    rw [committee.origin] at encode
    have opposite := (IsLinearMap.mk' _ (notationL C.path d (F) (L) N p 0)).map_neg y
    have obs : initial (L) C.path N p (-y) 0 U = -initial (L) C.path N p y 0 U := congrFun opposite U
    change ((S N).bar M (-y)).density 0 (L) ((R!) N) U = _
    rw [track.starts,((born.2 (-y)).2.1)]
    change Z.density 0 (L) ((R!) N) U+((M.tone N).plays (-y)).density 0 (L) ((R!) N) U = _
    rw [cream.booking U,show ((M.tone N).plays (-y)).density 0 (L) ((R!) N) U=_ from encode,obs]
    ring
  · intro i lower upper
    exact ⟨(key i lower upper _).2.1,(key i lower upper _).2.2,(wallet i lower upper).trans cream.dom⟩

end YM.Integration.WilsonAddressedEquationAtWindow
