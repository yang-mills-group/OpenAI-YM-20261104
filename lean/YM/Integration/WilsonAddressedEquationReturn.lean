import YM.Integration.WilsonAddressedEquationCourse

/-! The signed native Haar-equation discrepancy on the true cutoff and
each intermediate physical representation of that same discrepancy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedEquationReturn
open Filter Lattice Wilson Labels RG Push Source Extra.Histories Extra.Histories.Relay
open RG05Readout.Aligned MergeProof Bid WilsonAddressedEquationShelf
open scoped Classical
variable {G:Gauge} {C:Family G} {d N p:ℕ} {V:SectionData (C.labels.level d)}
variable {W:Bid.Worth} {u ψ:ℕ→ℝ} {ζ:ℕ→ℕ→ℝ}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "L"=> C.localSection d
local notation "R!"=> C.path.rep N p

theorem paid (real:C.Makes) {j:(F).Index} {E:ℝ} {x:C.label d}
    (income:Issued C V N p W u ψ ζ D j E x) :
    ∃ (field:∀ i,Coefficient (F) (C.side i p)) (fee:ℕ→ℝ),
      (∀ U,(field N).density 0 (L) ((R!) N) U =
        ((C.S.a N:ℂ)^d)*(((R!) N).eval U:ℂ)*
          (initial V C.path N p (Size.axis F j) 0 U - initial (L) C.path N p x 0 U)) ∧
      (∀ i : ℕ, C.ref d ≤ i → i < N →
        (field i).density 0 (L) ((R!) i)=blast C.path N p i d ((field (i+1)).density 0 (L) ((R!) (i+1)))) ∧
      ∀ i : ℕ, C.ref d ≤ i → i ≤ N →
        (field i).Format 0 C.params ((R!) i) ∧
        (field i).remBound 0 ((R!) i) (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (fee i) ∧
        gainChart C.path N i*(fee i+(F).coeffSize (field i).x) ≤ E := by
  obtain ⟨Z,t,q,_,cream,M,committee,S,track,label⟩ := income
  have ident : x = (S (C.ref d)).a := (C.factory d N p).terminal.injective label
  let Q := dualize C.path N p M (C.ref d) N S (-x)
  refine ⟨Q.voice,Q.cost,?_,fun i lo hi=>track.transfer i lo hi (-x),?_⟩
  · intro U
    have top := committee.sessions.sung.earned N track.admissible le_rfl
    have born := originate (L) C.path N p C.params M (m:=N) le_rfl real.wilson top
      track.opens track.funds (le_refl ((F).coeffSize Z.x+t))
    have encode := (real.calibrated d N p track.admissible).encode (-x) U
    rw [committee.origin] at encode
    have opposite := (IsLinearMap.mk' _ (notationL C.path d (F) (L) N p 0)).map_neg x
    have obs : initial (L) C.path N p (-x) 0 U = -initial (L) C.path N p x 0 U := congrFun opposite U
    change ((S N).bar M (-x)).density 0 (L) ((R!) N) U = _
    rw [track.starts,((born.2 (-x)).2.1)]
    change Z.density 0 (L) ((R!) N) U+((M.tone N).plays (-x)).density 0 (L) ((R!) N) U = _
    rw [cream.booking U,show ((M.tone N).plays (-x)).density 0 (L) ((R!) N) U=_ from encode,obs]
    ring
  · intro i lo hi
    have key := keys (L) C.path N p C.params M (-x) (track.traces.chairs i lo hi)
      (committee.sessions.sung.earned i lo hi)
    refine ⟨key.2.1,key.2.2,?_⟩
    have bill := track.expenses i lo hi
    rw [←ident] at bill
    exact bill.trans cream.dom

end YM.Integration.WilsonAddressedEquationReturn
