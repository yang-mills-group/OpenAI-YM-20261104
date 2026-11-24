import YM.Integration.WilsonMovingForkReporterPanelCourse

/-! An arbitrary finite bought interval, retaining every jointly assigned table. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterWalletWindow
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d:ℕ}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
variable {F:Extraction.Order}{S:Table C.book}(U:Final C F S)(a:(Cells.standard C).Hierarchy)
variable (simple:G.Simple)(fund:Scrim C W u ψ φ δ (fly C.path.levels) r L)
    {z:ℝ}(earns:∀i≤d,generator G i≤z)

variable (P:ℝ→Fin 3→Tapes.Panel d) (a0:Fin 3→ℝ) (width κ:ℝ) (base:5<a0 0)
variable (axes:∀s∈Icc 0 width,∀j,(P s j).arc=a0 j+s ∧
  (P s j).currency=(P 0 j).currency ∧ (P s j).θ=(P 0 j).θ)
variable (checks:∀s∈Icc 0 width,Checks (a0 0+s) (a0 1+s) (a0 2+s) κ (MergeProof.East.trays d) d)
include U simple fund earns base axes checks

theorem chunk (u:ℝ)(inside:u∈Icc 0 width):
    ∀ᶠ k in atTop,∀ s∈Icc 0 width,s∈Icc u (u+1) →
    ∀Y,PoisedSky (P s) B H O J (MergeProof.East.trays d) z k Y →
      TimberSky F a d k d (a0 0+s) κ Y:=by
  classical
  let Bad(k:ℕ):Prop:=∃s:ℝ,s∈Icc 0 width ∧ s∈Icc u (u+1) ∧
    ∃Y,PoisedSky (P s) B H O J (MergeProof.East.trays d) z k Y ∧ ¬TimberSky F a d k d (a0 0+s) κ Y
  let point(k:ℕ):ℝ:=if h:Bad k then h.choose else u
  have domain(i):point i∈Icc 0 width ∧ point i∈Icc u (u+1):=by
    by_cases h:Bad i
    · simp only [point,dif_pos h]; exact ⟨h.choose_spec.1,h.choose_spec.2.1⟩
    · simp only [point,dif_neg h]; exact ⟨inside,le_rfl,by linarith⟩
  by_contra no
  have hits(i:ℕ):∃k≥i,Bad k:=by
    by_contra! misses
    apply no
    filter_upwards [eventually_ge_atTop i] with k lo s hs hu Y bought
    by_contra lost
    exact misses k lo ⟨s,hs,hu,Y,bought,lost⟩
  choose k above bad using hits
  have late:Tendsto k atTop atTop:=tendsto_atTop_mono above tendsto_id
  let fee(i:ℕ):=point i-u
  have valid(i):fee i∈Icc (0:ℝ) 1:=by
    dsimp [fee]; obtain ⟨lo,hi⟩:=(domain i).2;constructor <;> linarith
  let Q(i:ℕ):=P (point i)
  let b(j:Fin 3):=a0 j+u
  have arcs(i j):(Q i j).arc=b j+fee i:=by
    change (P (point i) j).arc=(a0 j+u)+(point i-u)
    rw [(axes _ (domain i).1 j).1];ring
  have charged:ArcSky Q:=⟨⟨b,fee,valid,fun j i=>arcs i j⟩,
    fun j=>⟨_,fun i=>(axes _ (domain i).1 j).2.1⟩,
    fun j=>⟨_,fun i=>(axes _ (domain i).1 j).2.2⟩⟩
  have chooseRow(i):∃Y,PoisedSky (Q (k i)) B H O J (MergeProof.East.trays d) z (k i) Y ∧
    ¬ TimberSky F a d (k i) d (a0 0+point (k i)) κ Y:=by
    simpa only [Q,point,dif_pos (bad i)] using (bad i).choose_spec.2.2
  choose Y registered rejected using chooseRow
  have receipt:=WilsonMovingForkReporterPanelCourse.registered B H O J U a simple fund earns Q charged b
    fee valid arcs κ (checks _ inside) (base.trans_le (le_add_of_nonneg_right inside.1)) k late Y registered
  obtain ⟨i,ok⟩:=receipt.exists
  apply rejected i
  have rebase : b 0 + fee (k i) = a0 0 + point (k i) := by dsimp [b,fee]; ring
  rwa [rebase] at ok

theorem original (nonneg:0≤width):
    ∀ᶠ k in atTop,∀ s∈Icc 0 width,
    ∀Y,PoisedSky (P s) B H O J (MergeProof.East.trays d) z k Y →
      TimberSky F a d k d (a0 0+s) κ Y:=by
  have paid(j:Fin (⌊width⌋₊+1)):=chunk B H O J U a simple fund earns P a0 width κ
    base axes checks (j.val:ℝ) ⟨Nat.cast_nonneg _,(Nat.cast_le.mpr
      (Nat.le_of_lt_succ j.isLt)).trans (Nat.floor_le nonneg)⟩
  filter_upwards [eventually_all.mpr paid] with k all s hs
  let j:Fin (⌊width⌋₊+1):=⟨⌊s⌋₊,Nat.lt_succ_of_le (Nat.floor_le_floor hs.2)⟩
  exact all j s hs ⟨Nat.floor_le hs.1,(Nat.lt_floor_add_one s).le⟩

end YM.Integration.WilsonMovingForkReporterWalletWindow
end
