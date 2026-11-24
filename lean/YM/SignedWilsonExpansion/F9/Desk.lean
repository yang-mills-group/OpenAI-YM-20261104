import YM.SignedWilsonExpansion.F9.Docket
import YM.SignedWilsonExpansion.F9.GradesW
/-!
# Run-length desk. WCU phase & `Salary`s on the exact issued clocks
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics
open Stair MergeTrip Looms
variable (W':Initialize G)(F:Frames G)(Q:∀ h,Rays G h W'.hol){Ω:Council F}
variable {P':Hol G}{ι:Type}
-- filter receipts on geometry scheduled before conditioning levels
structure PorchK (Ω:Council F)(R:Realm G (e+1) E)(h k u:ℕ) extends Epic W' F Q Ω R h k u where
     b : ℕ
     v : ℕ
     r : ℕ
     berth : m ≤ b
     desk : b ≤ v
     endo : v≤c
     cost : Canopy R l c Z
     dat : l ≤ m
     datum : l ≤ r
     landing : r ≤ v
     pos : 0<ρ
     small :sizeT R.draws ρ v≤1
variable {W' F Q}
namespace PorchK
variable (x:PorchK W' F Q Ω R h k u) (q:ι→ PorchK W' F Q Ω R h k u)(Wn : Normalize.Store G)
variable {Y B:ι→ℝ} {L:Filter ι}{t0 U0:ι→ℝ}{z':InkQ}
abbrev canv : MergeTrip Ω (launch F W'.hol W'.surveys Q k) R.draws R.paid x.m x.b x.v x.c x.c h e k u x.Z:=⟨x.paid,x.berth,x.desk,x.endo⟩
def Annual (θ:ι→ PorchK W' F Q Ω R h k u)(L:Filter ι)(Y:ι→ℝ):Prop:= (Maxer L Y)∧ Wage L Y (1:ι→ℝ) (fun i=>(θ i).Z)
variable (hQ:Annual q L Y)
noncomputable abbrev πMark (i:ℕ):= sizeT R.draws x.ρ i
-- hours & budget support
abbrev ear (p:InkQ): InkQ:= northQ R.draws R.paid x.c x.l x.r p
abbrev starF := Stair.starFlight (relativeC R.draws R.paid x.c x.l (x.r-x.l))
lemma direction (x:PorchK W' F Q Ω R h k u)(p: FitsZ e z' t): FitsZ e (x.ear z') ((FitsZ.hairC G e E).buy x.Z*t):= (FitsZ.flight (x.cost.cut (le_refl x.l) x.datum (x.landing.trans x.endo)) (x.landing.trans x.endo) p).2 -- z' var
abbrev charge (n:ℕ)(L:Filter ι)(Y:ι→ℝ)(B:ι→ℝ)(X:ι→InkQ):Prop:=∀ i≤ n, Wage L Y B (fun a=> coeff i (X a))
lemma charge.term (C:Credit)(p:ι→InkQ)(hx: Wage L Y 1 U0)(T':∀ᶠ i in L,FitsZ e (p i) ((C.buy (U0 i))*B i)): charge e L Y B p:=by
    intro i hi; refine Wage.rel (show Wage _ _ _ (fun i=> C.buy (U0 i)*B i) from ?_) (IsBigO.of_norm_eventuallyLE (T'.mono fun a ha=>ha i hi))
    simpa using (Wage.mul (Wage.ornament C U0 hx) ( Wage.enroll (u:=Y) (isBigO_refl B L))) -- reducibility
private lemma FitsZ_of_sum (p:ι→InkQ): ∀ v:ι,FitsZ e (p v) (∑ j:Fin (e+1), ‖coeff j.val (p v)‖):=fun i j w=>Finset.single_le_sum (s:=Finset.univ) (f:=fun j: Fin (e+1)=> ‖coeff j.val (p i)‖) (fun j _=> norm_nonneg _) (Finset.mem_univ (⟨j,Nat.lt_succ_of_le w⟩:Fin (e+1)))
include hQ
lemma charge.ears (p:ι→InkQ)(f:charge e L Y B p): charge e L Y B (fun i=> (q i).ear (p i)):=by
    let D:= fun i=> (∑ j:Fin (e+1), ‖coeff j.val (p i)‖); have hv : Wage L Y B D:= Wage.sum hQ.1 _ _ (fun i _=> Wage.norm (f i.val (Nat.le_of_lt_succ i.isLt)))
    have hx:= charge.term (L:=L) _ (fun i=> (q i).ear (p i)) hQ.2 (B:=D) ( Eventually.of_forall fun i=> (direction (q i) (FitsZ_of_sum p i)) ); exact fun i u=> Wage.ascend (hx i u) hv
omit hQ
lemma charge.mul {a b:ι→ InkQ} (x:Maxer L Y)(u:charge e L Y B a)(p:charge e L Y t0 b): charge e L Y (B*t0) (fun i=>a i*b i):=by
    intro j w; simp only [coeff_mul]; exact Wage.sum x _ _ (fun i g=> by have ht:i.1+i.2=j:= (by simpa using g); exact Wage.mul (u i.1 (by omega)) (p i.2 (by omega)))
lemma charge.pow {a:ι→ InkQ} (x:Maxer L Y)(p:charge e L Y 1 a)(l:ℕ):charge e L Y 1 (fun i=>a i^l):=by
    induction l with| zero=> simp only [pow_zero]; exact fun i _=> Wage.unitC _ | succ l ih=> simp only [pow_succ]; simpa using charge.mul x ih p
include hQ
lemma storm : charge e L Y 1 (fun i=> (q i).starF):=by
   let F':= fun (_:ι)=> (PowerSeries.X:InkQ); have hv: charge e L Y 1 F':= fun i v=> Wage.unitC _; exact fun i v=> by apply Wage.fix (charge.ears (q:=q) hQ F' hv i v) (?_) (.refl ..); exact Eventually.of_forall fun j=> congr_arg (coeff i) (flightX _)
-- ζ Mark coherent through porch neighborhoods
abbrev χ (K:Rose.Pick Wn)(x:PorchK W' F Q Ω R h k u): InkQ:= recallH W' K R.draws R.paid x.c x.l x.r x.mesh
variable (K:Rose.Pick Wn)
variable (Pp:(∀ i≤ e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i)))
lemma chrono (f:RateQ.Costy L Y (fun i=> (q i).toEpic.voice W' K) e): charge e L Y 1 (fun i=> χ Wn K (q i)):= charge.ears q hQ _ (fun i p=> billed_wage (f i p))
include Pp
lemma sponsored (β:(F.level h).Index)(j:ℕ)(hv:j≤e): Salary L Y 1 ℂ (fun i=> (q i).canv.boots W' Wn (q i).mesh β (q i).l (q i).r (q i).ρ j):=by
     simp only [boots,Tape.tempo,LinearMap.coe_mk,AddHom.coe_mk]; apply Salary.many hQ.1; intro i t; have hx:=Finset.mem_range.mp t
     let D:= fun v' :ι=> (q v').starF
     have hT:Salary L Y 1 ℂ (fun j=>(q j).paid.lineTape W' Wn (q j).mesh (q j).l (q j).ρ β i):=by simp_rw [←published]; exact Across.salary ((Pp _ (by omega)).arrow (LinearMap.applyₗ ((F.level h).basis β)))
     simpa only [mul_one] using Salary.tilt (charge.pow hQ.1 (a:=D) (storm q hQ) i j hv) hT
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
