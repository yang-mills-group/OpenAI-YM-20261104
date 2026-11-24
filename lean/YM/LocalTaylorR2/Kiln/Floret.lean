import YM.LocalTaylorR2.Pavilion.ActPrincipal
/-!
 # Root-frame stencil for near path costs. Objective analytic expansion
 in the SAME local coarse and relative Lie variables as used for the
 rootface. Short (true inherited path length, additional cuts accounted
 separately) and retained street *and still keeping physical masks*.
 -/
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

def axis (S:StepData c f)(i:Trans f): Site c:= i.1.act (S.ratio.parent i.2.1)
local notation "valve" => Port.weightLog

def homeFoot (X:Coat T F)(A:ℕ→ Atom G d) (i:Trans f): Support c:= atomFoot S.ratio 0 X.B A i
def argument (J:Basecamp G)(X : Coat T F)(A:ℕ→ Atom G d) (i:Trans f)(u:Directions G f): ZipP G c f:=
    let a:= axis S i; let p:= point J X.χ (bed X) a X.V
    (p,fun j=> if atEdge S j∈ homeFoot X A i ∧ distAt S j a≤bed X then spinRow S (carrier a X.V) (X.signal u) j else 0)
def latent (A:ℕ→ Atom G d) (S:StepData c f)(i:Trans f)(x:ZipP G c f):= (A i.2.2).unmasked (pull i.1 0 (shaft S x)) i.2.1
def light (X:Coat T F)(A:ℕ→ Atom G d) (i:Trans f): Prop:= (A i.2.2).length≤ till X.x
def dim (X:Coat T F)(i:Trans f):Prop:= Inside (axis S i) X.seeds (200*X.B)
def opened (R:Rep G f)(A:ℕ→ Atom G d) (i:Trans f)(U:Config G f): Prop:= Healthy R.p.threshold ((A i.2.2).footprint i.2.1) (pull i.1 0 U)
def switch (R:Rep G f)(A:ℕ→Atom G d)(i:Trans f)(U:Config G f):ℝ:= if opened R A i U then 1 else 0

def pane (X:Coat T F)(a:ℝ)(A:ℕ→Atom G d)(i:Trans f)(u:Directions G f):= X.enforce (2*a) u (X.plaza (homeFoot X A i))
def pollen (J:Basecamp G)(X:Coat T F)(A:ℕ→Atom G d) (i:Trans f)(k:ℕ) (u:Directions G f): ℝ:= blockTaylor k (latent A S i) (argument J X A i u)

/-- Keep original sign and prefactor scalar `η`, Taylor model only within
   true short aperture. Raw masks, gaussian arguments and actual cutoff
   retained. DIM scenes cost can enter price comparisons with exact fields when
   needed; actual evaluation of retained vacuum terms will use empty roster and
   the bright model.
 -/
def lantern (J:Basecamp G)(X:Coat T F)(a η:ℝ)(A:ℕ→Atom G d) (R:Rep G f)(i:Trans f)(k:ℕ)(u:Directions G f): ℝ:= if light X A i then
    let U:= X.input u
    if dim X i then translateValue R.p A η U i * pane X a A i u else η*(pollen J X A i k u * switch R A i U)* pane X a A i u
    else 0
-- orientation and support. Follow true inherited stencil even on arbitrary periodic fields
-- (no pretending no-wrap).
lemma heart {l : ℕ} : axis S i ∈ atomFoot S.ratio l X.B A i:=by
  unfold axis atomFoot; rw [←affine0]; apply mem_image_of_mem; apply halo_subset; apply mem_image_of_mem; apply mem_union_left
  rw [Paths.atom_foot]; exact mem_insert_self ..
lemma pastturn {l:ℕ}{Z:Support c} (h: atomFoot S.ratio l X.B A i ⊆ Z) {x:Site c}(hj:x∈ homeFoot X A i): Cleanroom Z (l*X.B) x:= by
  intro t ht; obtain ⟨y,hY,he⟩ := mem_image.mp hj; obtain ⟨w,rfl⟩:= (StepData.sendSites i.1 0).surjective t; rw [← he, show StepData.sendSites i.1 (0:Site c) w=i.1.act w from affine0 ..,affine0,separation_signed] at ht
  apply h; apply mem_image_of_mem; obtain ⟨z,hz,hJ⟩:= halo_spec.mp hY; refine halo_spec.mpr ⟨z,hz,(separation_triangle z y w).trans ?_⟩; rw [zero_mul] at hJ; omega
lemma cursor {x : Bond f} (hx:x.1∈(A i.2.2).footprint i.2.1)(hq:x.1+step x.2∈(A i.2.2).footprint i.2.1)(P': Room P S T X.x)(he:light X A i):
   let j:= Channel.edge i.1 x
   atEdge S j∈ homeFoot X A i ∧ distAt S j (axis S i)≤bed X:=by
 intro j; unfold light at he
 have hyp (v: Site f) (h:v∈(A i.2.2).footprint i.2.1) (H:j.1=i.1.act v): atEdge S j∈ homeFoot X A i ∧ distAt S j (axis S i)≤bed X:=by
   rw [distAt,atEdge,H,S.ratio.parent_signed S.patch.odd_side]; refine ⟨?_,?_⟩
   · rw [← affine0]; apply mem_image_of_mem; apply halo_subset; apply mem_image_of_mem; exact mem_union_left _ h
   rw [axis,separation_signed]; rw [Paths.atom_foot] at h
   have hh: separation i.2.1 v≤ (A i.2.2).length:= Paths.where_slot _ _ _ h
   have hp:= Work.E04.parent_separation S.ratio i.2.1 v
   unfold till at he; unfold bed Coat.B; have hm:= P'.frame; omega
 cases hs:i.1.flip x.2
 · exact hyp _ hx (by unfold j; rw [positive _ _ hs])
 exact hyp _ hq (by unfold j; rw [negative _ _ hs])
lemma spotlight (A:ℕ →Atom G d) (i:Trans f) {U V:Config G f}
    (hh:Agrees ((A i.2.2).footprint i.2.1) (pull i.1 0 U) (pull i.1 0 V)) :
    (A i.2.2).unmasked (pull i.1 0 U) i.2.1=(A i.2.2).unmasked (pull i.1 0 V) i.2.1 :=by
  apply congr_arg (A i.2.2).poly; ext1 x; apply slot_local
  exact agrees_mono hh (fun y hy=> Finset.image_subset_image (show _⊆(A i.2.2).stencil from fun z hz=> mem_insert_of_mem (mem_biUnion.mpr ⟨_, mem_univ x,hz⟩)) hy)
lemma switching (R:Rep G f)(A:ℕ→Atom G d)(i:Trans f){U V:Config G f}(h: Agrees (inspected ((A i.2.2).footprint i.2.1)) (pull i.1 0 U) (pull i.1 0 V)): switch R A i U=switch R A i V:=by
  refine UsesFinal.allReads R.p.threshold _ (fun u=> if Healthy R.p.threshold ((A i.2.2).footprint i.2.1) u then (1:ℝ) else 0) ?_ _ _ h
  intro U V _ hk; dsimp only; unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty]; rw [hk]
lemma clearcost (R:Rep G f) (η:ℝ) (A:ℕ→Atom G d)(i:Trans f)(U:Config G f) : translateValue R.p A η U i=η*((A i.2.2).unmasked (pull i.1 0 U) i.2.1*switch R A i U):=by
 unfold translateValue switch opened Atom.placed masked; split_ifs <;> simp_all
end YM.LocalTaylorR2.Kiln
