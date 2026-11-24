import YM.SignedWilsonExpansion.F9.Flora
import YM.SignedWilsonExpansion.F9.Table
import YM.XSpace.Tamarack
/-!
# Evaluate *the same Wilson kernel* on orbit poses exactly
First via unengineered top Shelf after Wick and Ward restoration, then position recipe through field height. Include amount proof by physical arity/traces later.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Pill Cloth StationA
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec)
open Structure1 (HP)
section laws
open Maxwell (observable)
open Maxwell.Free
lemma indeed_own (d r:ℕ)(x:Label G k)(h:x∈ Labels.Grade (d,r)): MvPolynomial.IsWeightedHomogeneous scaleW (observable G k x) d:=by
    intro j h'; have hp : Finsupp.weight bwt j = (d,r):= channel h h'
    suffices hh:(Finsupp.weight bwt j).1=Finsupp.weight scaleW j by rw [←hh,hp]
    rw [Finsupp.weight_apply,Finsupp.weight_apply]; unfold Finsupp.sum; rw [Prod.fst_sum]; rfl
abbrev gated (F:Frames G)(x:(F.level h).Index) : HP G (wt (F.level h) x):= ⟨(bulb G _ (tag_name F x)).val,(bulb G _ _).property, indeed_own _ _ _ (StationA.known F x)⟩
abbrev vista (F:Frames G)(y:(F.level h).Index): Sec G h:=Normalize.en ((F.level h).bound y) (gated F y)
lemma carried (F:Frames G)(x:(F.level h).Index): vista F x=bulb G h ((F.level h).basis x):=by
    have hp:= (F.level h).bound x; let v:=wt (F.level h) x; set i:= downL F hp x (le_refl v); have h := climb F hp i; rw [show upL F hp i=x from up_down ..] at h
    rw [h]; rfl
lemma pressUp (F:Frames G)(v:h≤ d)(x:(F.level h).Index): vista F (upL F v x)=Normalize.up v (vista F x):=by rw [carried F,carried F,climb]; rfl
abbrev scenic (F:Frames G)(i: Stock F h): Sec G h:= Normalize.up (Nat.le_of_lt_succ i.1.isLt) (vista F i.2)
abbrev sun (F:Frames G)(i: Stock F h): ℕ:= wt (F.level _) i.2
end laws
section cards
variable (W: XSpace.Initialize G){x': ℕ}{Ω:Council F}
local notation "V"=> W.tree
variable {A'' : ∀ h,Rays G h W.hol}
variable (p':Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
variable (x:Sample (n+1))(L:Fin (n+1)→Cover)
lemma lampSight (i:Stock F h)(y:x.F.Sites): bespoken W.surveys F (V x.F.p) y i=((x.F.spacing:ℂ)^(sun F i)) • Rose.regal W h x y (scenic F i):=by
    let j:= sun F i; let z:= (gated F i.2); unfold scenic vista; rw [Normalize.en_up,Rose.regals,Initialize.atSite,LinearMap.smul_apply, smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (show (x.F.spacing:ℂ)≠0 from Complex.ofReal_ne_zero.mpr x.F.positive.ne')),one_smul]; rfl
lemma lampStill (t: Fin (n+1)→ Sec G d): LampNow (V x.F.p) (fun i=>Rose.regal W d x (chartV x i) (t i))=Tape.archive (live W d x) t:=by
    unfold Tape.archive; apply PowerSeries.ext; intro j; rw [coeff_mk,Rose.lit_up]; rfl
lemma scalarSight (T: x.F.p.Tree)(p:InkQ)(c:ℂ): Bare.scalar (G:=G) T (c • p)=c • Bare.scalar T p:=by
   rw [Algebra.smul_def,Algebra.smul_def]; unfold Bare.scalar; rw [map_mul]; -- AlgebraMap self_power
   rw [show algebraMap ℂ InkQ c= PowerSeries.C c from rfl]; exact congr_arg (fun v: Bare.Series T G=> v* Bare.scalar T p) (SameV.self_power T G c)
-- hand-off from hinge normalization. note dependence on sizeT A etc through through-h lantern.
def inkA (t':Mesh)(ρ:ℝ)(x:(F.level h).Index)(y:Stock F h): InkQ:= insertQ ((t'.spacing^(sun F y)) • p'.hymn ρ x y)
def bareTape (t':Mesh)(ρ:ℝ)(y:(F.level h).Index): Tape (Sec G h):= ∑ v: Stock F h,Tape.side (scenic F v) (p'.inkA W t' ρ y v)
include p'
theorem reveals (h' :∀ i, chartV x i=wrap x.F.p.side (L i))(y:Fin (n+1)→ (F.level h).Index)(ρ:ℝ): p'.galaxy (V x.F.p) L y ρ=Tape.tabular (live W h x) (fun i=>p'.bareTape W x.F ρ (y i)):=by
    let k:= V x.F.p; let U(i:Fin (n+1))(j:Stock F h):= Rose.regal W h x (chartV x i) (scenic F j)
    let Y(i:Fin (n+1))(v: Stock F h):= (x.F.spacing^(sun F v)) • p'.hymn ρ (y i) v
    let P(i:Fin (n+1))(v:Stock F h):= Bare.scalar k (insertQ (Y i v)) * U i v
    have hx (i:Fin (n+1))(j:Stock F h): Bare.scalar k (insertQ (p'.hymn ρ (y i) j))*bespoken W.surveys F k (wrap x.F.p.side (L i)) j= P i j:=by
       unfold P U k; rw [lampSight W, h' i, mul_smul_comm]; unfold Y; rw [show insertQ (((x.F.spacing)^sun F j) • (p'.hymn ρ (y i) j))= ((x.F.spacing:ℂ)^sun F j) • insertQ (p'.hymn ρ (y i) j) from (?_), scalarSight]; rw [smul_mul_assoc] -- smul_mul
       apply PowerSeries.ext; intro p; rw [inked,map_smul, map_smul,inked]; simp only [smul_eq_mul, Complex.ofReal_mul,Complex.ofReal_pow]
    unfold bareTape galaxy; change LampNow k (fun i=> ∑ j:Stock F h, Bare.scalar k (insertQ (p'.hymn ρ (y i) j))*bespoken W.surveys F k (wrap x.F.p.side (L i)) j)=_; simp_rw [hx]
    rw [LampNow.tabulates (G:=G) k Y U, MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro j _; rw [Tape.table_side, lampStill]; rfl
end cards
end Stair
end YM.WilsonCoeffUV.Mer.Xa
