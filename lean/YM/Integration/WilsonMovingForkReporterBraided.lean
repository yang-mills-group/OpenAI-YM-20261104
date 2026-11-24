import YM.Integration.WilsonMovingForkReporterFilament

/-! Both observed apertures on a single source-matched growing table, without a second physical extraction. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBraided
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {D E:ℕ→ℕ} {V:∀i,Vane C (D i)} {W:∀i,Vane C (E i)}
  {f:Extraction.Order} {H:(Bel C.book).Hierarchy}
open WilsonMovingForkReporterRestriction

def alternating {X:Type*} (a b:ℕ→X) (i:ℕ):X := if i%2=0 then a (i/2) else b (i/2)

theorem converges {X:Type*} {l:Filter X} {a b:ℕ→X} (ones:Tendsto a atTop l)
    (twos:Tendsto b atTop l):Tendsto (alternating a b) atTop l := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨u,hu⟩:=eventually_atTop.mp (ones.eventually_mem hs)
  obtain ⟨v,hv⟩:=eventually_atTop.mp (twos.eventually_mem hs)
  filter_upwards [eventually_ge_atTop (2*(u+v))] with i enough
  change (if i%2=0 then a (i/2) else b (i/2))∈s
  split
  · exact hu _ (by omega)
  · exact hv _ (by omega)

structure Pair (V:∀i,Vane C (D i)) (W:∀i,Vane C (E i)) where
  pick : ℕ→ℕ
  cofinal : StrictMono pick
  outer (i:ℕ) : 2*i≤D (pick i)
  inner (i:ℕ) : 2*i+1≤E (pick i)
  separate (i:ℕ) : (W (pick i)).wheel.r < (V (pick i)).wheel.r
  crossed (i:ℕ) : (V (pick (i+1))).wheel.r < (W (pick i)).wheel.r

theorem select (before:Tendsto D atTop atTop) (after:Tendsto E atTop atTop)
    (vanish:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0))
    (distinct:∀ᶠ i in atTop,(W i).wheel.r < (V i).wheel.r): Nonempty (Pair V W):=by
  have next (i j:ℕ):∃p:ℕ,j<p ∧ 2*i≤D p ∧ 2*i+1≤E p ∧
      (W p).wheel.r<(V p).wheel.r ∧ (V p).wheel.r<(W j).wheel.r := by
    have all:=((((eventually_gt_atTop j).and (before.eventually_ge_atTop (2*i))).and
      (after.eventually_ge_atTop (2*i+1))).and distinct).and (vanish.eventually (gt_mem_nhds (W j).wheel.rad))
    exact (all.mono (fun _ h=>⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩)).exists
  choose p past left right apart below using next
  let q:ℕ→ℕ:=Nat.rec (p 0 0) (fun i prev=>p (i+1) prev)
  refine ⟨⟨q,strictMono_nat_of_lt_succ (fun i=>past (i+1) (q i)),?_,?_,?_,fun i=>below (i+1) (q i)⟩⟩
  · intro i; cases i with
    | zero=>exact left 0 0
    | succ i=>exact left (i+1) (q i)
  · intro i; cases i with
    | zero=>exact right 0 0
    | succ i=>exact right (i+1) (q i)
  · intro i; cases i with
    | zero=>exact apart 0 0
    | succ i=>exact apart (i+1) (q i)

def Pair.report (c:Pair V W) (i:ℕ):Vane C i :=
  if h:i%2=0 then
    vane (d:=i) (by have l:=c.outer (i/2);omega) (V (c.pick (i/2)))
  else vane (d:=i) (by have l:=c.inner (i/2);omega) (W (c.pick (i/2)))

private lemma same {M:ℕ→ℕ} {A:∀j,Vane C (M j)} {d i j:ℕ} (eq:i=j) (f:d≤M i) (g:d≤M j):
    vane f (A i)=vane g (A j) := by cases eq;rfl

theorem even (c:Pair V W) (i:ℕ): c.report (2*i) = vane (c.outer i) (V (c.pick i)) := by
  rw [Pair.report,dif_pos (show 2*i%2=0 by omega)]
  exact same (A:=fun j=>V (c.pick j)) (by omega) _ _

theorem odd (c:Pair V W) (i:ℕ): c.report (2*i+1) = vane (c.inner i) (W (c.pick i)) := by
  rw [Pair.report,dif_neg (show (2*i+1)%2≠0 by omega)]
  exact same (A:=fun j=>W (c.pick j)) (by omega) _ _

theorem earned (c:Pair V W) (sold:∀i,(V i).checked f H (D i))
    (bought:∀i,(W i).checked f H (E i)) (i:ℕ): (c.report i).checked f H i := by
  unfold Pair.report
  split
  · exact checked _ _ (sold _)
  · exact checked _ _ (bought _)

theorem calendar (c:Pair V W) (a:Tendsto (fun j=>(V j).k) atTop atTop)
    (b:Tendsto (fun j=>(W j).k) atTop atTop):Tendsto (fun i=>(c.report i).k) atTop atTop := by
  apply (converges (a.comp c.cofinal.tendsto_atTop) (b.comp c.cofinal.tendsto_atTop)).congr
  intro i
  unfold alternating Pair.report
  split <;> rfl

theorem opens (c:Pair V W) (a:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0))
    (b:Tendsto (fun i=>(W i).wheel.r) atTop (𝓝 0)):
    ∃X:Zoom,∀i,X.r i=(c.report i).wheel.r := by
  let g i:=(c.report i).wheel.r
  refine ⟨⟨g,fun i=>(c.report i).wheel.rad,strictAnti_nat_of_succ_lt ?_,?_⟩,fun _=>rfl⟩
  · intro i
    change (c.report (i+1)).wheel.r < (c.report i).wheel.r
    let j:=i/2
    by_cases hi:i%2=0
    · have he:i=2*j:=by dsimp [j];omega
      rw [he,even,odd]
      exact c.separate j
    · have he:i=2*j+1:=by dsimp [j];omega
      rw [he,show 2*j+1+1=2*(j+1) by omega,even,odd]
      exact c.crossed j
  · apply (converges (a.comp c.cofinal.tendsto_atTop) (b.comp c.cofinal.tendsto_atTop)).congr
    intro i
    unfold g alternating Pair.report
    split <;> rfl

end YM.Integration.WilsonMovingForkReporterBraided
end
