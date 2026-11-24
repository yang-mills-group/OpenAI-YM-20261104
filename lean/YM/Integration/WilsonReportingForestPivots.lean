import YM.Integration.WilsonPhysicalRegisteredForestCrossing
import YM.Integration.WilsonReportingRegisteredForest
import YM.Integration.WilsonReportingForestBlocks
import YM.Work.E01

/-! Purchase all free links of each touched original coarse block and both
orientations of its boundary. Each distinct ordered pair of coarse parents
keeps a single actual fine bond as its shared exterior coordinate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Filter Finset Set Metric Lattice Wilson Tree RG RG16 MSbar.Heath Precision PertExtension OPE.Therm
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonPhysicalRegisteredForestCrossing
open WilsonReportingRegisteredAction WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f}

def chooseBond (T:Forest S.ratio) (q:Site c × Site c) (h:∃a:T.Free,parents T a=q) : T.Free:=h.choose

def pivot (T:Forest S.ratio) (e:T.Free) := chooseBond T (parents T e) ⟨e,rfl⟩

theorem pair_of (T:Forest S.ratio) (e:T.Free) : parents T (pivot T e)=parents T e :=
  Classical.choose_spec (show ∃a:T.Free,parents T a=parents T e from ⟨e,rfl⟩)

theorem shared (T:Forest S.ratio) {e a:T.Free} (h:parents T e=parents T a) : pivot T e=pivot T a := by
  simp only [pivot,h]

def internal (T:Forest S.ratio) (e:T.Free):Prop:=(parents T e).1=(parents T e).2

def moving (T:Forest S.ratio) (B:Finset T.Free) : Finset T.Free := B.filter fun e=>internal T e ∨ e≠pivot T e

theorem saved (T:Forest S.ratio) (B:Finset T.Free) (e:T.Free) (h:¬ internal T e) : pivot T e∉moving T B := by
  intro he
  rcases (Finset.mem_filter.mp he).2 with h'|h'
  · exact h (by simpa only [internal,pair_of] using h')
  · exact h' (shared T (pair_of T e)).symm

def background (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (e:↥(moving T B)):G.El:=if h:internal T e.val then 1 else v ⟨pivot T e.val,saved T B e.val h⟩

def deviation (T:Forest S.ratio) (u:T.Slice G) (e:T.Free) : G.El:=if internal T e then u e else u e*(u (pivot T e))⁻¹

variable (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path.levels

def incident {m per:ℕ} (T:Forest ((A).clock.op m per).ratio) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per)) : Finset T.Free :=
  Finset.univ.filter fun e=>∃(i:I) (z:Site (R.family.side (m+1) per)),z∈(R.family.localSection (d i)).footprint (o i) ∧
    (((A).clock.op m per).ratio.parent z=(parents T e).1 ∨ ((A).clock.op m per).ratio.parent z=(parents T e).2)

def faces (m per d:ℕ) (o:Site (R.family.side (m+1) per)) :=
  let L:=((A).clock.op m per).ratio.count.val
  WilsonAxialWindow.cells o (radius (extent (depth R d+3) L) L)

def cold (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per)) : Set (Config G (R.family.side (m+1) per)) :=
  ⋂i,House.chilly (G:=G) (faces R m per (d i) (o i)) (cool (A) (m+1))

/-- The registered footprint which meets either endpoint's true parent is a
common anchor for every bond with those same ordered parents. -/
theorem anchored {m per:ℕ} (T:Forest ((A).clock.op m per).ratio) (d:I→ℕ)
    (o:I→Site (R.family.side (m+1) per)) (e:T.Free) (he:e∈incident R T d o) :
    ∃i:I,∀b:T.Free,parents T b=parents T e→
      let D:=extent (depth R (d i)+3) ((A).clock.op m per).ratio.count.val
      separation (o i) b.val.1≤D ∧ separation (o i) (b.val.1+step b.val.2)≤D := by
  obtain ⟨i,z,hz,side⟩:=(Finset.mem_filter.mp he).2
  refine ⟨i,?_⟩;intro b same
  have center:=reaches R (d i) (o i) z hz
  let L:=((A).clock.op m per).ratio.count.val
  let x:=b.val.1;let y:=b.val.1+step b.val.2
  have xy:separation x y≤1:=Work.E01.sep_step_le _ _
  have yx:separation y x≤1:=by rw [separation_comm];exact xy
  change separation (o i) x≤depth R (d i)+3+8*L+1 ∧ separation (o i) y≤depth R (d i)+3+8*L+1
  rcases side with h|h
  · have q:((A).clock.op m per).ratio.parent z=((A).clock.op m per).ratio.parent x:=h.trans (congrArg Prod.fst same).symm
    have short:separation z x≤8*L:=neighbors T q
    have l:=separation_triangle (o i) z x;have r:=separation_triangle (o i) x y;omega
  · have q:((A).clock.op m per).ratio.parent z=((A).clock.op m per).ratio.parent y:=h.trans (congrArg Prod.snd same).symm
    have short:separation z y≤8*L:=neighbors T q
    have l:=separation_triangle (o i) z y;have r:=separation_triangle (o i) y x;omega

/-- Every free bond incident on a touched block can be decoded in the
original group chart relative to its one held ordered-parent representative. -/
theorem chart (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) {r:ℝ} (pr:0<r) (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,
    ∀per (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).clock.op m per).ratio) (u:T.Slice G), T.drape u∈cold R m per d o→
    (fun e:↥(moving T (incident R T d o))=>deviation T u e.val)∈Chart.chamber G _ r := by
  let D (i:I):=depth R (d i)+3
  let H:=Finset.univ.sup D
  let ε:=min J.δ (r/(2*J.C))
  have pc:=zero_lt_one.trans_le clear.cost
  have ep:0<ε:=lt_min clear.dist (div_pos pr (by positivity))
  filter_upwards [WilsonReportingForestBlocks.dates R.family simple slow H (half_pos ep)] with m prices per o T u good
  intro e _
  obtain ⟨i,near⟩:=anchored R T d o e.val (Finset.mem_filter.mp e.property).1
  obtain ⟨period,buy,_⟩:=prices per (D i) (Finset.le_sup (f:=D) (Finset.mem_univ i))
  let L:=((A).clock.op m per).ratio.count.val
  let bound:=area (extent (D i) L) L*cool (A) (m+1)
  have pt:0≤cool (A) (m+1):=by unfold cool RG.Calendar.hatCoupling;positivity
  have capped:G.chord (deviation T u e.val)≤ε:=by
    have half:bound≤ε/2:=buy
    by_cases h:internal T e.val
    · have l:=near e.val rfl
      have b:G.chord (u e.val)≤bound:=free T (o i) _ period u pt (Set.mem_iInter.mp good i) e.val l.1 l.2 h
      simpa only [deviation,if_pos h] using b.trans (half.trans (half_le_self ep.le))
    · have b:G.chord (u e.val*(u (pivot T e.val))⁻¹)≤2*bound:=pair T (o i) _ period u pt (Set.mem_iInter.mp good i) e.val (pivot T e.val)
          (pair_of T e.val).symm (fun f hf=>near f (hf.elim (fun z=>z ▸ rfl) (fun z=>z ▸ pair_of T e.val)))
      rw [deviation,if_neg h];linarith only [b,half]
  have dec:=clear.near _ (capped.trans (min_le_left ..))
  have cm:J.C*(r/(2*J.C))=r/2:=by field_simp
  refine ⟨J.decode _,?_,dec.2.1⟩;rw [mem_ball_zero_iff]
  exact dec.2.2.trans_lt ((mul_le_mul_of_nonneg_left (capped.trans (min_le_right ..)) pc.le).trans_lt (cm.trans_lt (half_lt_self pr)))

end YM.Integration.WilsonReportingForestPivots
