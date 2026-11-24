import YM.Integration.WilsonOriginalObservedRoseBadge

/-! Restore the first derivative from the seven original signed receipts on the same joint panel. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseLedger

open Function Filter Finset Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Precision
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open WilsonMaxwellThermometerPublicStation (report)
open WilsonOriginalNullReleasedMaximalLimit
open WilsonPositionGradedThermometerHearing (offer)
open WilsonMaxwellThermometerFiniteTangent (credit roster)
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (D:ChartRatio G) (W:Initialize G) {V:Normalize.Store G} (K:Rose.Pick V)
variable {f:Extraction.Order} {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy} {S:Table R.family.book}
variable (F:Final R.family f S) (J:ℝ→tower S) (A:ℝ→Group R.family 6)
abbrev Visit := ℝ×(ℕ×ℕ)
local notation "fit" => WilsonPositionCorrectedCap.adjusted F J V A
local notation "k" => fun r=>(fit r).station.k
local notation "cut" => trail.curry (Y:Filter (ℕ×ℕ))
variable (mesh:ℝ→Mesh) (v:Visit→∀i,Axes R i) (u:Visit→Sec G 6) (a b:Visit→Sec G 4) (axis:Visit→ℝ)
local notation "tags" => fun w:Visit=>deposited R (k w.1) w.1 w.2.2 (v w)
local notation "ref" => fun w:Visit=>roster (u w) (a w) (b w)

def due (w:Visit) (s:Finset (Fin 3)) : ℂ :=
  if h: k w.1 ≤ w.2.1 then
    WilsonOriginalObservedRoseBadge.receipt R D W K F J A w.1 w.2 h (mesh w.1) (tags w) (ref w) (axis w) s
  else 0

def higher (w:Visit) : ℂ :=
  if h: k w.1 ≤ w.2.1 then
    (WilsonOriginalObservedRoseJoint.fees R D W K F J A w.1 w.2 h (mesh w.1) (tags w) (ref w) (axis w)).2
  else 0

/-- Each hypothesis concerns a dated signed ordinary face or a genuine finite Taylor coefficient. -/
theorem original (simple:G.Simple) (shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (book:Book (f:=f) (l:=Y) (H:=H) A J) (lead:Leading F J) (q:ℕ) (prior:(Y:Filter _)≤f.fuse)
    (solved:∀ᶠ w in cut,∀i,Solved R (fit w.1) q w.2.1 w.2.2 univ i (v w i))
    (law:LocalRatio D) (hot:∀ᶠ w in cut,0<axis w)
    (ground:Tendsto (fun w=>credit W K (mesh w.1) (u w) (a w) (b w)/(axis w:ℂ)) cut (𝓝 0))
    (paid:∀s:Finset (Fin 3), s.Nonempty →
      Tendsto (fun w=>due R D W K F J A mesh v u a b axis w s/(axis w:ℂ)) cut (𝓝 0))
    (orders:Tendsto (fun w=>(axis w:ℂ)*higher R D W K F J A mesh v u a b axis w) cut (𝓝 0)) :
    Tendsto (fun w:Visit => offer F J V K A w.1 w.2/(axis w:ℂ)) cut (𝓝 (Rose.c_T K:ℂ)) := by
  have before : ∀ᶠ w:Visit in cut,k w.1≤w.2.1 := by
    apply eventually_curry_iff.mpr
    exact Eventually.of_forall fun r=>(large_mesh f (k r)).filter_mono prior
  have faces (s:Finset (Fin 3)) :
      Tendsto (fun w=>due R D W K F J A mesh v u a b axis w s/(axis w:ℂ)) cut (𝓝 0) := by
    rcases s.eq_empty_or_nonempty with e|e
    · subst s
      apply (tendsto_const_nhds (x:=(0:ℂ))).congr'
      filter_upwards [before] with w issued
      rw [due,dif_pos issued,WilsonOriginalObservedRoseBadge.empty,zero_div]
    · exact paid s e
  have total : Tendsto (fun w=>∑s:Finset (Fin 3),due R D W K F J A mesh v u a b axis w s/(axis w:ℂ))
      cut (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun s _=>faces s)
  have first:=WilsonMaxwellThermometerReleasedSlope.original R W K F J A simple shop book lead q prior v solved
  have combined:=((ground.add first).add total).add orders
  simp only [zero_add,add_zero] at combined
  refine combined.congr' ?_
  filter_upwards [before,hot] with w h pos
  have eqn:=WilsonOriginalObservedRoseJoint.original R D W K F J A law w.1 w.2 h (mesh w.1)
    (tags w) (u w) (a w) (b w) (axis w)
  dsimp only at eqn
  rw [WilsonOriginalObservedRoseBadge.original] at eqn
  change _ + _ + (∑s:Finset (Fin 3), due R D W K F J A mesh v u a b axis w s/(axis w:ℂ)) +
      (axis w:ℂ)*higher R D W K F J A mesh v u a b axis w = _
  simp only [due,higher,dif_pos h,←Finset.sum_div]
  have nz : (axis w:ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  field_simp [nz]
  linear_combination -eqn

end YM.Integration.WilsonOriginalObservedRoseLedger
