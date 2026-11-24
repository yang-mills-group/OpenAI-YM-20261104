import YM.Qlocal.Reckoner.Stature
import YM.Qlocal.Flight
/-! Connecting the EOS Temp projection to **actual** POLY under stable
 cost. Cohesive on all Ω.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V I Ω J J' J₀ K α:Type}[DecidableEq V][DecidableEq I]{G:Gauge}{n:Side}{R:Census I}
variable {X: RG.Rep G n}{s:V→ Support n}{s':I→Support n} {A A' B B' u v a t w δ:ℝ} {o: V→Site n}{o':I→Site n}
lemma Night.settled {u:Source G n Ω R}{q:Ray R}(r:Rental q)(h:Night X s' u q t A)(ht:0≤t)(x:Ω)(y:Config G n): Summable (Merge.Photo.fronts X.activities (fun i=> u x i y) y X.p):=by
 obtain ⟨f,h₀,h⟩:=h.cost; exact RG03.Gather.gas_series (A:=X.activities) (fun _ : I=>zero_lt_one) (h₀.summable_units r ht (fun i=> (X.activities.forced i).inventory_ne.mono (X.activities.forced i).inventory_sup) (fun i=> h x i y) (fun _=>1) (fun _=>zero_lt_one))
namespace Translation
open Planet Scribe
variable [Fintype V]
set_option quotPrecheck false
local notation "Ψ"=> Whole V
variable (T:V→R.Mode) (f:Ω→V→ℂ) (hp:∀ i,(T i).val.Nonempty) (hO:∀ i v,v∈(T i).val → s' v⊆ s i)
local notation "P"=> fun x:Ω=> morph T (f x) hp
variable {q:Ray R}{q':Ray (Whole V)}(S:Scribe Ω J G n (Whole V))(T':Scribe Ω J' G n (Whole V))(E:Scribe Ω J₀ G n (Whole V))(r:Rental q)(r':Rental q')
local notation "S'"=> scribe T f
local notation "Ψ₀"=> (fun x: Ω=> (P x))
variable [Fintype I]
variable (K':Source G n Ω (Whole V)) (h0: Night X s K' q' t A)
    (hS:S.Proper X.p s) (hu:S.Spend X.p q' t B) (ht:0≤t)
local notation "Y"=>Translation.lift T f hp K'
include h0 hS hu hp r' ht in
lemma transports (x:Ω)(y:Config G n): density X (S' S) Y x y=(P x) (density X S K' x y):= by
 let W:= P x; let L':Poly (Whole V)→L[ℂ]Poly R:= LinearMap.toContinuousLinearMap W.toLinearMap; let q:=Scribe.cost_read hu r' hS ht x y; let p':=Scribe.calm_send hu r' hS ht x y
 have ht': W (S.send X.p x y)=(S' S|>.send X.p x y):= (L'.map_tsum q).trans (tsum_congr (fun i=> vocals T f hp S ..)) -- application params reorder
 have hk' : W (Poly.pass (S.send X.p x y))= Poly.pass ((S' S).send X.p x y):= (Multi.pass_map W _ p' ((preserveQ ..).trans p')).trans (congr_arg Poly.pass ht')
 let K := Merge.Photo.fronts X.activities (fun i=> K' x i y) y X.p; let Z:= Merge.Photo.fronts X.activities (fun i=> Y x i y) y X.p; have hy(i): W (K i)= Z i:= by unfold K Z Merge.Photo.fronts; split; exact map_prod W ..; exact map_zero _
 unfold density session; simp only [map_smul,map_mul]; rw [show W (Poly.pass _)=_ from hk']; congr 2; exact Eq.symm ((L'.map_tsum (h0.settled r' ht x y)).trans (tsum_congr hy)) -- direction & align

omit [Fintype I] in
lemma scribe_pairs : scribe T f (pile S T')= pile (S' S) (S' T'):= by
 unfold scribe pile; simp only [Scribe.mk.injEq]; refine ⟨funext (fun i=>?_ ),trivial,trivial,?_⟩; cases i <;> rfl; funext x i; cases i <;> rfl -- prop ext
include r r' hp hO ht
-- separate weighting for cert; renderer.L. Keep separate prices at chosen reference scale after projection.Differential. Zero costs on sectors which truly disappear thanks to hom.
variable {V' : Ω→ Config G n → Poly (Whole V)} {q'' : Ray (Whole V)}
variable {m0 e0 e1 r0 r1 t0 s0 u0 v0 z0:ℝ}
lemma connects (z':Rental q'')
    (h:Certified X s q' t A B δ v S T' E K' V')
    (hM:S.Spend X.p q'' t m0) (he:T'.Spend X.p q'' t e0)(hT:E.Spend X.p q'' t t0)
    (hz:Check T f S q'' q u0)(hc:Check T f T' q'' q r0)(hh:Check T f E q'' q z0)(hQ:News T f q' q A')
    (he1:0≤u0) (he2:0≤r0)(hE:0≤z0)(hw:0≤A'): Certified X s' q t (A'*A) (u0*m0) (r0*e0) (z0*t0) (S' S) (S' T') (S' E) Y (fun x v=> (P x) (V' x v)):= by
 obtain ⟨p₀,h0,p₁,h1,p₂,h2,hK,hH⟩:= h; refine ⟨ aspects T f hp hO S p₀, funds T f S r z' hM hz he1, aspects T f hp hO T' p₁,funds T f T' r z' he hc he2,aspects T f hp hO E p₂,funds T f E r z' hT hh hE,silver T f hp hO r r' hK hw hQ,?_⟩ -- adjust `funds` explicit
 funext x y; rw [← hH,← scribe_pairs,← scribe_pairs]; exact transports T f hp _ r' K' hK (p₀.pile (p₁.pile p₂)) (Spend.pile h0 (Spend.pile h1 h2)) ht x y
omit hO ht r r'
open Pressure Tree ConnectedActivityE6 ConnectedActivityE6.Channel  
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent PhysicalNext PhysicalNext.Repeat Lotus Footprint StageArt
variable {f' c' L:Side}{R0:RG.Rep G f'}{F':StepData c' f'}{Z₀:Teller G}{O:ConnectedActivityE6.Target G Z₀}
    {D:Tube G F'}{W β μ C₀:ℝ}{Q':Target.Order G W}{D0:Ω→ α→Lotus.Leaf R0}
variable (M:Cash W β μ L O Q' C₀ D R0) [Fintype α] (g:α→ℝ)(D₀:α↪V)
include hp
open Next.Fluctuations Push.SectorMeasure
lemma mounts (x) (y:Config G f') : (P x) (Photo.given (S:=F') (D0 x) g (Whole V) (fun i=> Planet.glyph (D₀ i)) y)= Photo.given (S:=F') (D0 x) g R (fun i=> Poly.send (T (D₀ i)) (f x (D₀ i))) y:= by
 unfold Photo.given; simp_rw [map_sum,map_smul,map_prod]; exact sum_congr rfl fun i _=> congr_arg (fun v:Poly R=> _ • v) (Finset.prod_congr rfl (fun i _=> Translation.issues ..)) -- explicit
include M
lemma commutes (x) (y:Config G c') : (P x) (F'.push R0.beta (Photo.given (S:=F') (D0 x) g (Whole V) (fun i=> Planet.glyph (D₀ i))) y)= F'.push R0.beta (Photo.given (S:=F') (D0 x) g R (fun i=> Poly.send (T (D₀ i)) (f x (D₀ i)))) y:= by
 have hY: F'.IsKernel R0.beta G:= F'.isKernel (funds_branch M.laws.intake.ready) _
 let Z := Photo.given (S:=F') (D0 x) g (Whole V) (fun i=> Planet.glyph (D₀ i)); have ht : Integrable Z (prior G f'):=by unfold Z Photo.given; refine integrable_finsetSum _ fun i _=>?_ ; exact ((((Palette.team _ i).sells M.laws.intake.cap).1.integrable _).mul_const _).smul_const _
 let L':Poly (Whole V)→L[ℂ] Poly R:= LinearMap.toContinuousLinearMap (P x).toLinearMap; let E':=L'.restrictScalars ℝ; have he:= E'.integral_comp_comm (StepData.push_slice hY y Z ht); simp_rw [E'.map_smul] at he; unfold StepData.push; refine he.symm.trans ?_; refine integral_congr_ae (Eventually.of_forall (fun v=>?_)); dsimp only; rw [← mounts T f hp g]; rfl -- inspect
end Translation
end YM.Qlocal.Reckoner
