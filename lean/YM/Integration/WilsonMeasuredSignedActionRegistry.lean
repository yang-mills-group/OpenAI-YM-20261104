import YM.Integration.WilsonMeasuredSignedActionPhysical
import YM.Integration.WilsonMovingForkHeterogeneousCut

/-! The original action may occupy any slot of the grade-four restrictions
of the registered roster. Each cutoff uses the matrix from that same file,
elected before evaluating any of its deletion or self faces. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionRegistry
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
    {T:Campaign R}(L:Pillars R T)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4

def weak {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H Z D T r)(h:4≤D)(J:PhysMS.tower S)(z:ℕ×ℕ):(C).label 4:=
  let i:Fin (D+1):=⟨4,Nat.lt_succ_of_le h⟩
  ((B.rows i).arm true (J 4 (stepField C))).source z

def axisVote {n K:ℕ}(file:Filed R (fun _:Fin n=>4) K)(slot:Fin n)(z:ℕ×ℕ)(Y:(C).label 4):(C).label 4:=
  (file.A z.1 z.2 slot).symm (fitted R 4 (file.station slot) z.1 z.2 Y)

def HeardAt (j N per:ℕ)(Y:(C).label 4):Prop:=
  ∀{n target:ℕ}(_old:0<n)(top:j+n≤N){η:ℝ}
    (A:(C).label 4≃ₗ[ℂ](C).label 4)(_width:1≤((C).path.levels.budget j).supportExponent)
    (_sale:∀x,Arrived R 4 j (j+n) N per target (by omega) top η A x),
    ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ (A.symm (fitted R 4 j N per Y)))=(s:ℂ) • axis F₀

private theorem restation {j i K N per target:ℕ}{η:ℝ}
    {A:(C).label 4≃ₗ[ℂ](C).label 4}{Y:(C).label 4}
    {old:i≤K}{past:j≤K}{top:K≤N}(eqn:i=j)
    (issued:Arrived R 4 i K N per target old top η A Y): Arrived R 4 j K N per target past top η A Y:=by
  subst i
  exact issued

theorem atFile {n j K N per:ℕ}(file:Filed R (fun _:Fin n=>4) K)(slot:Fin n)(Y:(C).label 4)
    (home:file.station slot=j)(later:j<K)(top:K<N)(wide:1≤((C).path.levels.budget j).supportExponent)
    (earned:HeardAt R j N per Y):
    ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ (axisVote R file slot (N,per) Y))=(s:ℂ) • axis F₀:=by
  obtain ⟨p,rfl⟩:=Nat.exists_eq_add_of_le later.le
  have positive:0<p:=by omega
  have sold(x:(C).label 4):Arrived R 4 j (j+p) N per file.target (by omega) top.le (1/32)
      (file.A N per slot) x:=by
    exact restation R home (file.arrived N per top slot x)
  unfold axisVote
  change ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ ((file.A N per slot).symm (fitted R 4
    (file.station slot) N per Y)))=(s:ℂ) • axis F₀
  rw [home]
  exact earned positive top.le (file.A N per slot) wide sold

theorem raised {d j K N per target:ℕ}{η:ℝ}(same:d=4)(Y:(C).label d)(A:(C).label d≃ₗ[ℂ](C).label d)
    (later:j<K)(top:K≤N)(wide:1≤((C).path.levels.budget j).supportExponent)
    (issued:∀x,Arrived R d j K N per target later.le top η A x)
    (earned:HeardAt R j N per (same ▸ Y)):
    ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ (same ▸ A.symm (fitted R d j N per Y)))=(s:ℂ) • axis F₀:=by
  subst d
  obtain ⟨p,rfl⟩:=Nat.exists_eq_add_of_le later.le
  exact earned (show 0<p by omega) top A wide issued

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    {J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (frame:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g)
    (X:Zoom){D T:ℕ→ℕ}(B:∀m,Book F (l:=l) H Z (D m) (T m) (X.r m))
    (roof:∀m,m≤(B m).k)(stages:Tendsto (fun m=>(B m).W.k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀ i:4≤D m,∀ᶠ z:ℕ×ℕ in f.fuse,
      HeardAt R (B m).W.k z.1 z.2 (weak R F (B m) i (J (X.r m)) z):=
  WilsonMeasuredSignedActionPhysical.original R F L simple bliss frame cal heat X B roof stages

end YM.Integration.WilsonMeasuredSignedActionRegistry
end
