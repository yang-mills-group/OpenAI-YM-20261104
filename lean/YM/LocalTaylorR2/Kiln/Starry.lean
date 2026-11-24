import YM.LocalTaylorR2.Kiln.Season

/-! # Power formula for every retained path LOG. Coefficients computed before output, hold all hard and profile factors. FAR inside vs outside is here a real locality cost; do not disregard K-in-actual-vacuum. See Local ledger. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary Candle Mesh Port Pavilion RG01.Survive
variable {W C μ:ℝ}{Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}

lemma dark_is_extension (Z: Molecule S)(hp:LocalTaylorR2.Pure Z): (roster Z).place=∅:=by
 have H : Z.toLeft=∅:= eq_empty_iff_forall_notMem.mpr (fun i hi=>by obtain ⟨v,he⟩:= hp _ (mem_toLeft.mp hi); cases he)
 rw [← Packets.place_reads,Matter.register,H]; simp

variable (H : Cash W s μ L Q o C T R)
def synth (_H: Cash W s μ L Q o C T R)(A:ℕ→ Atom G d)(i:Trans f)(η:ℝ)(p:ℕ): Port.Test T:= fun _ X w=>
  let u:=worldZ X R.beta w; if light X A i then η*(pollen (Canvas.primary G) X A i (p+3) u * switch R A i (X.input u))* pane X o.a A i u else 0
lemma bright (w:Air f G)(h:X.seeds.place=∅)(A:ℕ→ Atom G d)(i:Trans f)(η:ℝ)(p:ℕ): Kiln.flame H η A i (p+3) F X w=synth H A i η p F X w:=by
  have hh: ¬ dim X i :=fun h'=>by obtain ⟨v,hv,-⟩:= halo_spec.mp (show _∈_ from h'); simp only [h,notMem_empty] at hv
  unfold Kiln.flame synth; simp only [lantern,if_neg hh]

-- On the primitive representation (before Held-U transportation/re-expression or any subtraction). Match branch voltage actual at this occurrence to the simplified local formula.
def realLens (_H:Cash W s μ L Q o C T R)(p:ℕ)(i:Coat.Stream c f): Port.Test T:= fun _ X w=>let u:=worldZ X R.beta w; -R.beta * Raw.orientation * (X.enforce (2*o.a) u (X.booth (rowSite S i))*Canvas.rootTaylor (Canvas.primary G) X i (p+2) u + tune (Canvas.primary G) X i (p+2))
lemma look (p:ℕ)(i:Coat.Stream c f)(w:Air f G)(h:X.seeds.place=∅) : cub H p (.inr (.inl (.inl i))) F X w= realLens H p i F X w:=by
  have hh:¬ Inside (rowSite S i) X.seeds (200*X.B):= fun h'=>by obtain ⟨v,hv,-⟩:= halo_spec.mp (show _∈_ from h'); simp only [h,notMem_empty] at hv
  change Canvas.pineCone (Canvas.primary G) X _ R _ _ _ - Pavilion.delta ..= _
  unfold Canvas.pineCone Pavilion.delta realLens; simp only [if_neg hh,Pavilion.tune,voltageV]; ring

def optic (p:ℕ)(i:LogIndex c f):Port.Test T:= match i with
| .inl (.inr (.inl i)) => synth H R.path.cubic i (-Raw.orientation*R.beta) p
| .inl (.inr (.inr (.inl i))) => synth H R.path.quartic i (-Raw.orientation*R.beta) p
| .inl (.inr (.inr (.inr (.inl i)))) => synth H R.path.loop i (-Raw.orientation) p
| .inr (.inl (.inl i)) => realLens H p i
| _ => mosaics H p i
lemma glance (i : LogIndex c f)(w:Air f G)(h:X.seeds.place=∅)(p:ℕ): cub H p i F X w=optic H p i F X w:= by
  rcases i with (i | (i| (i|(i|i))))| (i|i) | i
  · rfl
  · exact bright H w h ..
  · exact bright H w h ..
  · exact bright H w h ..
  · rfl
  · exact look _ _ _ w h
  all_goals rfl
/-- On OCCURRENCE arguments, `preps` on the roster for episode. No DIM at call in the vacuum (even though it may return on a differently-spotted mark with its own receipts). -/
lemma motif (Z:Molecule S)(q : Paint Z p)(i:Coat T F)(k:S.Choices)(Y:F.Slice G)(w:Air f G)(he:Clear Z) (h:chooseSlot q≠perch p): let u := (((preps i (roster Z)).taggedL k).wrapY Y)
    warm H ((resting G).symbol H p) q F u w = ∏ v:↥(logs Z), (optic H p v.val F u w)^Series.rank (q v)/((Series.rank (q v)).factorial:ℝ) := by
 intro u; unfold Mesh.warm; refine prod_congr rfl (fun l _=>?_); change absorb (q l) _ (cub H p l.val F u w) = (optic H p l.val F u w)^ _ / _; rw [lights h l,glance H l.val w (show u.seeds.place=∅ from dark_is_extension _ (isPure he)) p]
end YM.LocalTaylorR2.Kiln
