import YM.Integration.WilsonReportingForestPivots

/-! Genuine charged sites for varying the occupied internal and relative
crossing coordinates, before any old cutoff, field or period is drawn. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Filter Set Finset Lattice RG Wilson Tree RG16 OPE.Therm PhysicalNext.Repeat.Legato
open WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks WilsonReportingRegisteredAction
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path.levels

def sites (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per)) : Support (R.family.side (m+1) per) :=
  Finset.univ.biUnion fun i=>(faces R m per (d i) (o i)).image Prod.fst

theorem support (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m)) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀per (o:I→Site (R.family.side (m+1) per)),
    let Y:=sites R m per d o
    (Y.card:ℝ)≤(A).clock.hatBeta (m+1)^2 ∧
    ∀(T:Forest ((A).clock.op m per).ratio) e,e∈moving T (incident R T d o)→e.val.1∈Y ∧ e.val.1+step e.val.2∈Y := by
  let D (i:I):=depth R (d i)+3
  let H:=Finset.univ.sup D
  have grows:=(Next.Rank.Station.hat_rate (A) simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonReportingForestBlocks.dates R.family simple slow H (ε:=1) zero_lt_one,
    grows.eventually_ge_atTop (Fintype.card I:ℝ)] with m raw roster per o
  dsimp only
  let b:=(A).clock.hatBeta (m+1)
  change (Fintype.card I:ℝ)≤b at roster
  let L:=((A).clock.op m per).ratio.count.val
  have price (i:I):((faces R m per (d i) (o i)).card:ℝ)≤b :=
    (raw per (D i) (Finset.le_sup (f:=D) (Finset.mem_univ i))).2.2 (o i)
  have body (i:I) (x:Site (R.family.side (m+1) per)) (h:separation (o i) x≤extent (D i) L):x∈sites R m per d o := by
    let face:PlaqAxes:=⟨(0,1),by decide⟩
    have big:separation (o i) x≤radius (extent (D i) L) L:=by unfold radius;omega
    have p:=WilsonAxialWindow.cell (o i) _ (Work.E08.lift_mem_box big) face
    rw [wrap_lift,sub_add_cancel] at p
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,Finset.mem_image.mpr ⟨(x,face),p,rfl⟩⟩
  constructor
  · have sum:(sites R m per d o).card≤∑i:I,((faces R m per (d i) (o i)).image Prod.fst).card:=Finset.card_biUnion_le
    calc
      ((sites R m per d o).card:ℝ)≤∑i:I,(((faces R m per (d i) (o i)).image Prod.fst).card:ℝ):=by exact_mod_cast sum
      _≤∑_i:I,b:=Finset.sum_le_sum (fun i _=>(by exact_mod_cast Finset.card_image_le (s:=faces R m per (d i) (o i)) (f:=Prod.fst) : (((faces R m per (d i) (o i)).image Prod.fst).card:ℝ)≤(faces R m per (d i) (o i)).card).trans (price i))
      _=(Fintype.card I:ℝ)*b:=by simp
      _≤b^2:=by rw [sq];exact mul_le_mul_of_nonneg_right roster (((A).fits.delayed _).le.trans' zero_le_one)
  · intro T e he
    obtain ⟨i,near⟩:=anchored R T d o e (Finset.mem_filter.mp he).1
    have both:=near e rfl
    exact ⟨body i e.val.1 both.1,body i _ both.2⟩

end YM.Integration.WilsonReportingForestPivots
