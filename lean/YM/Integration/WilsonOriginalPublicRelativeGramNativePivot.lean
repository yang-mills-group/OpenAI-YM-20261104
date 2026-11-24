import YM.Integration.WilsonOriginalPublicRelativeGramNativeLaw

/-! The normalized independent finite Wilson pivot is read on the true f
children, in the units of its own original mesh ruler. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativePivot
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalPublicRelativeGramPosted (Dated gram)
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered)
open WilsonOriginalPublicRelativeGramNativeSites (sample)
open WilsonOriginalPublicRelativeGramPlanted (file)
open WilsonPositionProgramTrialOpticalBand (Band Bracket)
open scoped Topology Classical

variable {G:Gauge}(R:Run G)(D:XSpace.Run)
structure Ruler where
  cut:ℕ→ℕ
  stage:ℕ
  board:Band R D cut stage
  turn:ℝ→ℕ
  cofinal:Tendsto turn trail atTop
  place:ℝ→ℕ
  live:∀r,place r≤cut (board.reporter+turn r)
  fine:Tendsto (fun r=>R.family.S.a (place r)/R.family.S.a (board.reporter+turn r)) trail (𝓝 0)

namespace Ruler
variable {R D}(L:Ruler R D)
def station (r:ℝ):ℕ:=L.board.reporter+L.turn r
def scale (r:ℝ):ℝ:=R.family.S.a (L.station r)
def mesh (r:ℝ):ℕ:=L.board.mesh (L.turn r)
def top (r:ℝ):ℕ:=L.cut (L.station r)
theorem gauge (r:ℝ):R.family.S.a (L.top r)=L.scale r*(D.step (L.mesh r)).spacing:=by
  have yes:=L.board.spacing (L.turn r)
  change R.family.S.a (L.top r)/L.scale r=(D.step (L.mesh r)).spacing at yes
  rw [←yes]
  field_simp [show L.scale r≠0 from (R.family.S.a_pos _).ne']
theorem late:Tendsto L.station trail atTop:=tendsto_atTop_mono
  (fun r=>Nat.le_add_left (L.turn r) L.board.reporter) L.cofinal
theorem small:Tendsto L.scale trail trail:=tendsto_nhdsWithin_iff.mpr ⟨R.family.S.shrinks.comp L.late,
  Eventually.of_forall (fun _=>R.family.S.a_pos _)⟩
end Ruler

variable (pres:WilsonPrescription G)(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(avoid:Finset E4)
    (L:Ruler R pres.run)
local notation "I" => Glyph B h
local notation "d" => (fun _:I=>h)
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "Board" => Dated (L:=Unit) R pres.scheme (fun _:Glyph B h=>h)
def exposure (r:ℝ)(paper:Board):Board:=
  {paper with
    nodes:=fun _ _=>sample R avoid (pointsAt a) (pres.run.step (L.mesh r)) (L.live r) (L.scale r) (L.scale r)
    mass:=fun _ _=>1
    g:=fun z=>regulatorRun R.family z.1 z.2 (L.top r)}

def filed (q:ℕ)(r:ℝ)(paper:Board):Board:=
  file pres B h a R (exposure R pres B h a avoid L r paper) q (L.mesh r)

variable (ℓ:Ultrafilter (ℕ×ℕ))(paper:ℝ → Dated (L:=Unit) R pres.scheme (fun _:Glyph B h=>h))(q:ℕ)
local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))
variable {simple:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(verified:Main.Match pres simple M T dial)

theorem first {Z₀:Type}(l:Filter Z₀)(inside:Z₀→Filter (ℕ×ℕ)):
    Tendsto Prod.fst (ordered l inside) l:=by
  intro u hu
  change ∀ᶠr in l,∀ᶠ_ in inside r,r∈u
  filter_upwards [show ∀ᶠr in l,r∈u from hu] with r hr
  exact Eventually.of_forall (fun _=>hr)

include verified in
theorem original {f:Extraction.Order}(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse){A:ℝ}(ap:0≤A)(cut:Bracket R L.cut A):
    Tendsto (fun p:Z=>gram R pres.scheme d (filed R pres B h a avoid L q p.1 (paper p.1)) p.2)
      real (𝓝 (maxwell B h a)):=by
  let money:=WilsonOriginalPublicRelativeGramKineticMesh.thermal R
  obtain ⟨warm,cold,span,actual⟩:=WilsonOriginalPublicRelativeGramKineticMesh.original R simple
    pres.run L.board ap cut L.turn L.cofinal
  let ν:=fun r=>exposure R pres B h a avoid L r (paper r)
  have pose:=WilsonOriginalPublicRelativeGramNativeSites.original R avoid (pointsAt a)
    (fun r=>pres.run.step (L.mesh r)) L.place L.top L.live L.scale L.scale (gain:=1)
    (Eventually.of_forall fun r=>⟨R.family.S.a_pos _,R.family.S.a_pos _,L.gauge r⟩)
    L.fine (by
      apply (tendsto_const_nhds (x:=(1:ℝ))).congr
      intro r
      exact (div_self (R.family.S.a_pos _).ne').symm)
  apply WilsonOriginalPublicRelativeGramPlanted.original pres B h a R ℓ ν q L.mesh verified
    (Eventually.of_forall warm) cold 2 (4*A) (by norm_num) span
  · have entry:=pose.2.comp (first trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ))))
    change Tendsto (fun p:Z=>familiar (sample R avoid (pointsAt a) (pres.run.step (L.mesh p.1)) (L.live p.1) (L.scale p.1) (L.scale p.1))) real (𝓝 (WilsonPositionProgramPublicReflectedRead.lower a))
    rw [one_smul] at entry
    rw [WilsonPositionProgramPublicReflectedRead.placement]
    convert entry using 1 <;> rfl
  · change ∀ᶠr in trail,∀ᶠz in (ℓ:Filter (ℕ×ℕ)),_ ∧ _ ∧ _ ∧ _
    filter_upwards [actual] with r price
    filter_upwards [WilsonOriginalPublicRelativeGramNativeLaw.reference ℓ below (L.top r)] with z live
    exact ⟨rfl,pose.1 r,rfl,price z.1 z.2 live⟩

end YM.Integration.WilsonOriginalPublicRelativeGramNativePivot
