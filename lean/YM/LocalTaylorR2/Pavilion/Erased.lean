import YM.LocalTaylorR2.Canvas.ScenicBook

/-!
 # Canvas : expand ALSO the analytic Gaussian-reference mean adjustment.
 Goal is true argument Taylor before doing propagation. Here: dry spine compatibility with vacuum stencil. Pay interpolation separately.
 Erasing extrusion at recovery point (not setting V to 1 in the integral).
 Not removing flags/profiles; projected models preserve all engineering.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Pavilion
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o0 : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R: Rep G f}{X X':Coat T F}{J:Canvas.Basecamp G}{b a γ W α y' ζ d v q μ u C :ℝ}{χ:Chi}{j i' l :ℕ}
variable {Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}{H : Cash W s μ L Q o C T R}
open Canvas Mesh Port Work.G05 Animals Itinerary Reserves
lemma zeroed (X : Coat T F)(u:ZipP G c f): (dry X u).saved=0:=by
  funext j; unfold saved; exact if_pos (or_iff_not_imp_left.mpr (fun h=> (X.no_flat j).2 h))
lemma awning (t : Site c→ G.El)(X:Coat T F)(p:P.Funds S T)(h:ShellAccess S G X.x W X.width γ)(i: Coat.Stream c f): let Y:=sluice X t
    Vine.costs Y (voltage Y) i.1 i.2=Vine.costs X (voltage X) i.1 i.2:=by
  dsimp only; rw [(fastens X p h t).2.2]; exact (upwind X t p h (voltage X) i.1 i.2 true).2
lemma desiccated (X:Coat T F)(Y:F.Slice G)(i: Coat.Stream c f)(u:ZipP G c f):
    let Z := dry X u; let A:= dry (X.wrapY Y) u
    Vine.costs Z (voltage Z) i.1 i.2=Vine.costs A (voltage A) i.1 i.2:=by
  intro Z A
  have he (i t) (v:Directions G f): strain Z t i v=strain A t i v:=by unfold strain signal; rw [show Z.saved=_ from zeroed X u,show A.saved=_ from zeroed _ u]; rfl
  have hs : bar Z 0=bar A 0:=by funext i; unfold bar; rw [he]; rfl
  have hv : voltage Z= voltage A:=by unfold voltage well leanB; rw [hs]; rfl
  unfold Vine.costs; rw [hv]; exact sum_congr rfl fun j hj=> by unfold Vine.pot; rw [he]; rfl

def pitch (J:Basecamp G)(X: Coat T F)(o:Site c) : ZipP G c f := (Canvas.point J X.χ (24*X.B) o X.V,0)
def drip (X: Coat T F)(u:ZipP G c f) := dry (X.wrapY 1) u
def meanV (X: Coat T F)(i : Coat.Stream c f) (u:ZipP G c f) := Vine.costs (drip X u) (voltage (drip X u)) i.1 i.2

def tune (J:Basecamp G)(X : Coat T F)(i:Coat.Stream c f)(l:ℕ) := if Inside (rowSite S i) X.seeds (200*X.B) then 0 else
    blockTaylor l (meanV X i) (Pavilion.pitch J X (rowSite S i))
def voltageV (X: Coat T F)(i:Coat.Stream c f) := if Inside (rowSite S i) X.seeds (200*X.B) then 0 else Vine.costs X (voltage X) i.1 i.2

lemma footing (J:Basecamp G)(X:Coat T F)(i:Site c)(z:Site c→G.El): pitch J (sluice X z) i= tinters (z i) c f (pitch J X i):=by
  apply Prod.ext; swap; · exact (map_zero (tint _ _)).symm
  funext j; change Canvas.point J X.χ _ _ (gauge z X.V) _= G.adjoint (z i) (Canvas.point J X.χ (24* X.B) i X.V j)
  unfold Canvas.point; change (@ite _ (separation i j.1≤ 24*X.B) _ _ _)=_; split
  next h=> rw [around z i X.V]; exact J.log.conjugate X.χ _ _
  next h=> rw [map_zero]
lemma rafters (X : Coat T F) (k:G.El)(z:ZipP G c f) :
    drip X (tinters k c f z) = sluice (drip X z) (fun _=>k):= by
  let p:= (fun _:Site c=>k); let y:= pairs (drip X z) p (1:F.Slice G)
  have he : y=1:=by funext j; change k*1*k⁻¹=1; group
  change _=((drip X z).rinse _).wrapY y; rw [he]; unfold drip dry rinse vary blank Coat.wrapY; dsimp only; congr 1; exact tint_one k z.1
lemma mean_colored (X:Coat T F)(i:Coat.Stream c f)(u:ZipP G c f)(k:G.El)(p:P.Funds S T)(h:ShellAccess S G X.x W X.width γ): meanV X i (tinters k c f u)=meanV X i u:=by
  unfold meanV; rw [rafters]; exact awning (fun _=>k) (drip X u) p h i
lemma pitch_fence (J:Basecamp G)(j : Site c)(h: Zone X X' j (120*X.B)) (hp:0<X.B) : pitch J X j=pitch J X' j:=by
  apply Prod.ext; swap; · rfl
  funext i; dsimp only [pitch]; rw [h.chi, ← show X.B=X'.B from congr_arg radiusB h.temp]; unfold Canvas.point; split
  next hi=> rw [admits h.pay (r:=24*X.B) (by omega) i hi]
  rfl
lemma parentish (i:Coat.Stream c f) (j:Rod c f) (h:j∈ parents i.2): root S (i.1,j)=rowSite S i:= by unfold root; rw [cost_is_here, (parent_iff ..).1 h]; rfl
lemma uncloud (X:Coat T F)(i:Coat.Stream c f)(h:¬ Inside (rowSite S i) X.seeds (200*X.B)) : Vine.costs X (voltage X) i.1 i.2=∑ j∈parents i.2, ‖message X (i.1,j)‖^2/2:=by
  refine sum_congr rfl fun j hj=>?_ ; apply if_pos; unfold selected addr
  rw [(parent_iff ..).1 hj]; apply Shell.clear h; change _+separation (rowSite S i) (rowSite S i) ≤_; rw [separation_self]; omega
lemma aside (i: Coat.Stream c f) (K : Zone X X' (rowSite S i) (24*X.B))(p:Room P S T X.x)
    (he:¬Inside (rowSite S i) X.seeds (200*X.B)) (he':¬Inside (rowSite S i) X'.seeds (200*X'.B)):
    Vine.costs X (voltage X) i.1 i.2=Vine.costs X' (voltage X') i.1 i.2:=by
  rw [uncloud X i he,uncloud X' i he']; apply sum_congr rfl; intro j hj
  apply congr_arg (fun x:G.Color=> ‖x‖^2/2); exact local_strain p K (i.1,j) (Eq.symm (parentish i j hj)) (by omega)
    _ _ (fun i' hi _=> local_voltage p (K.tune_down (q:=atEdge S i') (b:=17*X.B) (by unfold distAt at hi; omega)) i' rfl le_rfl)
lemma sapped (X:Coat T F)(v:ZipP G c f)(i:Coat.Stream c f)(h:Zone X X' (rowSite S i) (24*X.B))(p:Room P S T X.x): meanV X i v=meanV X' i v:= by
  apply aside i (p:=p) (X:=drip X v) (X':=drip X' v) _ (X.blank_no _ (200*X.B)) (X'.blank_no _ (200*X'.B))
  refine ⟨h.temp,h.width,h.chi,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,?_,?_⟩; exacts [h.site,h.bond]
lemma winded (X:Coat T F)(v:ZipP G c f)(i:Coat.Stream c f)(p:Room P S T X.x)(g: Site c→ G.El)(h:ShellAccess S G X.x W X.width γ)(he:¬ Inside (rowSite S i) X.seeds (200*X.B)) (hv: AgreeNear id (rowSite S i) (24*X.B) (gauge g X.V) (increment 1 v.1)): meanV X i v=Vine.costs X (voltage X) i.1 i.2:=by
  rw [← awning g X p.accepted h]; let Y:= sluice X g; let K:= dry Y v
  have hy : drip X v=drip Y v:= rfl
  unfold meanV; rw [hy,drip, ← desiccated Y 1 i v]; symm
  exact aside i ⟨rfl,rfl,rfl,fun i' ht=> iff_of_false (fun hz=> he (Lattice.halo_spec.mpr
    ⟨i',hz,(separation_comm ..).trans_le (show separation (rowSite S i) i'≤ _ from ht.trans (by change 24*X.B≤200*X.B; omega))⟩))
    (fun hy=> Y.blank_no i' 0 (halo_subset _ _ hy)), fun _ _=>rfl,hv,fun _ _=>rfl,fun _ _=>rfl⟩ p he (Y.blank_no _ _)
end YM.LocalTaylorR2.Pavilion
