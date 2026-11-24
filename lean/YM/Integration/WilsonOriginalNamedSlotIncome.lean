import YM.Integration.WilsonOriginalNamedSlotChange
import YM.MergeProof.South.Admit
import YM.MergeProof.North.Clause

/-! Install the actual canonical physical coefficient in a chosen original
singleton slot. The full first variation bears precisely its native signed
one-source density on that face. All proper spectator records are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedSlotIncome
open Finset Function Marker Lattice Wilson RG Labels Source Extra.Histories
open MergeProof MergeProof.Accent WilsonForcedMarkerLine WilsonOriginalNamedSlotChange
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [Fintype V] [DecidableEq V] {J:Census V}

private theorem addCap {g h:ℕ → Config G n → ℂ} (hg:Dominated g) (hh:Dominated h) :
    Dominated (g+h) := by
  obtain ⟨a,sa,ha⟩:=hg
  obtain ⟨b,sb,hb⟩:=hh
  exact ⟨a+b,sa.add sb,fun j U=>(norm_add_le _ _).trans (add_le_add (ha j U) (hb j U))⟩

private theorem printed (P:Rep G n) {g h:ℕ → Config G n → ℂ} (hg:Dominated g) (hh:Dominated h) :
    profile P.activities (g+h)=profile P.activities g+profile P.activities h := by
  funext t U
  exact (Summable.tsum_add ((hg.summable U).subtype _) ((hh.summable U).subtype _))

variable (P:Rep G n) (F:V → Config G n → ℂ) (g:V → ℕ → Config G n → ℂ)
  {X:Config G n → Poly J} {o:V → Site n} {w:V → ℝ} {a b p₀ t₀:ℝ}
  {d:ℕ} {E:Frame G d} (T:SectionData E)
local notation "K" => (fun i=>profile P.activities (g i))

/-- A variation in one registered physical source. Its active singleton is the
literal signed group-field observable, including the eligible quiet partners. -/
theorem original (book:Served P F K X o w a b) (valid:P.activities.Valid P.p p₀ t₀)
    (stock:∀i,Dominated (g i)) (v:V) (q:Coefficient E n) {κ B:ℝ} (paid:q.remBound (o v) P κ B) :
    let f:= q.exponentialEntry (o v) T P
    let k:= profile P.activities q.forced
    ∃ Y:ℂ → Config G n → Poly J, Y 0=X ∧
      (∀z,Served P (tilt F v f z) (fun i s=>tilt (fun j=>K j s) v (k s) z i) (Y z) o w a b) ∧
      (∀z U,Line v z (X U) (Y z U) (Y 1 U)) ∧
      ∀U,(Y 1 U).part (J.fire v)=(X U).part (J.fire v)+q.density (o v) T P U := by
  intro f k
  obtain ⟨Y,empty,offered,line⟩:=WilsonOriginalNamedSlotChange.original P F K book v f k
  refine ⟨Y,empty,offered,line,?_⟩
  let next (i:V):ℕ → Config G n → ℂ:=if i=v then g i+q.forced else g i
  have budget:=rem_dominated paid
  have raised:∀i,Dominated (next i):=by
    intro i
    by_cases j:i=v
    · simpa only [next,if_pos j] using addCap (stock i) budget
    · simpa only [next,if_neg j] using stock i
  have eq:(fun i s=>tilt (fun j=>K j s) v (k s) 1 i)=(fun i=>profile P.activities (next i)):=by
    funext i B U
    by_cases j:i=v
    · simp only [next,tilt,if_pos j,one_mul,printed P (stock i) budget,Pi.add_apply,k]
    · simp only [next,tilt,if_neg j]
  have native:Served P (tilt F v f 1) (fun i=>profile P.activities (next i)) (Y 1) o w a b:=eq ▸ offered 1
  have fine:tilt F v f 1 v=F v+f:=by
    funext U
    simp [tilt]
  intro U
  rw [(native.relay raised valid U).1 v,fine,(book.relay stock valid U).1 v]
  simp only [next,if_pos rfl,Float.coin_plus P (F v) f (stock v) budget valid.boundK,Pi.add_apply]
  rw [coin_primary]

end YM.Integration.WilsonOriginalNamedSlotIncome
