import YM.LocalTaylorR2.Canvas.Ink

/-!
# Cauchy data in the oriented physical stencil.
 Includes all gauge transforms (even exterior). Does not move trajectory.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R:Rep G f}{X X':Coat T F}{b a γ W α y' ζ d q :ℝ}{χ:Chi}{j p' l :ℕ}
variable {w w':Air f G}{Z:Support c}{k k':Finset ℕ} {A : Basecamp G}
open Work.G05 Animals Itinerary

def tint (z:G.El)(c:Side): Directions G c→L[ℝ] Directions G c:= ContinuousLinearMap.pi (fun i: Bond c => (G.adjoint z).toContinuousLinearMap.comp (ContinuousLinearMap.proj i))
def tinters (z:G.El)(c f:Side): ZipP G c f →L[ℝ] ZipP G c f := (tint z c).prodMap (tint z f) 
lemma tint_one (x : G.El)(u:Directions G n) : increment 1 (tint x n u)=Lattice.gauge (fun _=>x) (increment 1 u):=by
  ext1 j; unfold increment Lattice.gauge; change G.lieExp (G.adjoint x (u j)) * 1=x*(G.lieExp (u j)*1)*_; rw [exp_adjoint,mul_one,mul_one]
lemma tilt (t : Site c→G.El) (V: Config G c) (u : Directions G f): increment (replica S.ratio (gauge t V)) (spinRow S t u)=gauge (constantGauge t S.ratio) (increment (replica S.ratio V) u):=by
  rw [← copied _ S.patch.odd_side]; ext1 i; unfold Lattice.gauge; simp only [increment,spinRow,exp_adjoint]
  unfold constantGauge atEdge; simp only [Function.comp_apply]; group
lemma crewed (h:P.Funds S T)(A:ZipP G c f)(x:G.El)(i:Spot c f)(q:S.Choices) : ivy T s q i (tinters x c f A)= ivy T s q i A:=by
  let t : Site c→ G.El:=fun _=>x; let L:= increment (1:Config G c) A.1
  obtain ⟨_,_,hq,-⟩:= h.feeds
  change squarepot _ _ _ (increment (replica S.ratio (increment 1 (tint x c A.1))) (spinRow S t A.2)) (increment 1 (tint x c A.1)) (spinRow S t A.2) _=squarepot _ _ _ _ _ _ _
  rw [tint_one]; change squarepot T s q (increment (replica S.ratio (gauge t L)) (spinRow S t A.2)) (gauge t L) _ i= squarepot _ _ _ _ L _ _
  rw [tilt t L, squarepot,squarepot,show increment (replica S.ratio L) A.2=shaft S A from rfl,winds t (shaft S A) L h] -- shaft reducible?
  apply congr_arg₂ (·-·) rfl
  apply sum_congr rfl; intro j _; rw [peony t h,under T hq, ← map_add,G.norm_adjoint]
lemma angle (h:ShellAccess S G X.x W X.width γ) (J:Basecamp G) (X':Site c→ G.El) (i:Coat.Stream c f)(w:Directions G f):
    arbor J (sluice X X') i (spinRow S X' w) = tinters (X' (rowSite S i)) c f (arbor J X i w) :=by
  let s:=i.1; let o:=lead S i.2; let V:=pull s 0 X.V; let t:Site c→G.El:=fun v=>X' (s.act v); let u:= t o
  have hp : pull s 0 ((sluice X X').V)= gauge t V:=by change pull s 0 (Lattice.gauge  X' X.V)=_; rw [Work.F05.pull_gauge_zero]; simp_rw [affine0]; rfl
  have hv : displacement s ((sluice X X').signal (spinRow S X' w)) (replica S.ratio (sluice X X').V)= spinRow S t (displacement s (X.signal w) (replica S.ratio X.V)):= by rw [pockets X h]; exact rotated_input ..
  apply Prod.ext
  · funext j; change point J X.χ (bed X) o _ j= G.adjoint u (point J X.χ (bed X) o V j)
    rw [hp]; unfold point; split
    next hj=> rw [around t o V]; exact J.log.conjugate X.χ _ _
    next hj=> rw [map_zero]
  funext j'; change (if distAt S j' o ≤ bed X then _ else 0)= G.adjoint u (if distAt S j' o≤bed X then _ else 0); split
  next hk=> rw [hp,hv]; unfold spinRow carrier; simp only [travel_gauge,deposits, ← G.adjoint_mul, inv_mul_cancel_right]; rfl
  next hk=> rw [map_zero]
lemma elevation (J:Basecamp G)(X:Coat T F)(R:Rep G f)(t:Site c→G.El)(p:P.Funds S T)(h:ShellAccess S G X.x W X.width γ)(i:Coat.Stream c f)(hd:ContDiffAt ℝ (↑j) (ivy T X.x (choice i.1 X.k) i.2) 0): pineCone J (sluice X t) a R i j (worldZ (sluice X t) R.beta (weep X t w))=pineCone J X a R i j (worldZ X R.beta w):=by
  have hp : rootTaylor J (sluice X t) i j (spinRow S t (worldZ X R.beta w))=rootTaylor J X i j (worldZ X R.beta w):=by
    unfold rootTaylor; rw [angle h]; exact blockTaylor_equivariant hd (tinters _ _ _) (ContinuousLinearMap.id ℝ ℝ) (Eventually.of_forall fun _=> crewed p _ _ _ _) _
  rw [Stained.flight X t p h]; unfold pineCone; dsimp only; rw [hp, Hues.mandate X t,(fastens X p h t).2.2, (Stained.upwind X t p h (voltage X) i.1 i.2 true).2]; rfl
end YM.LocalTaylorR2.Canvas
