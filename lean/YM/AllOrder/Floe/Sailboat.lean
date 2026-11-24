import YM.AllOrder.Floe.Bateau
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D:RG.Supply.Rolls X.p}(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) -- x stage fine from D
open Exterior Plateau.Line RG.Supply Roost
set_option quotPrecheck false
-- Ops.L from Paid: required orientation.
variable (A:Alloy X D) (F:Factor A)
local notation "E" => A.B.a
local notation "Xz" => A.B.a.clock.J (m+1)
local notation "Xy" => A.B.a.clock.J m
local notation "D₀"=>ConnectedActivityE6.loopBill G (D.L Xz) (A.B.a.clock.hatBeta m)
local notation "M"=> A.B.M
local notation "K"=> X.p.kernel
local notation "C₀"=>A.B.M.H N m
local notation "C₁"=>A.B.M.H N (m+1)
local notation "W"=> A.B.kin.path N (m+1)
local notation "V"=> (X.p.profile Xz).clip
local notation "P"=> Mural.sheet X.p D (A.B.a.clock.adm (m+1))
local notation "P'"=>Mural.sheet X.p D (A.B.a.clock.adm m)
local notation "ℒ"=> (A.B.a.S.block m)
variable (h:m<N)
open Iron
include h
local notation "Φ"=> X.K
local notation "w"=> (D.L Xz)
local notation "θ"=> R.pre k
local notation "U"=> starBo A m N
local notation "Zx"=> |(Φ).Ω Xz|
local notation "Zy"=> |(Φ).Ω Xy|
lemma strip_pay {Vx: ℕ} (hv:Vx≤N)(Wx : Side) : let i := A.B.a.clock.J Vx; let Y:= A.B.M.H N Vx; let Q:=X.K; (Y.metric.strip (Q.α i) (|Q.Ω i|)) ∧ Floor Y (X.p.profile (A.B.a.clock.J Vx)).clip Wx (Q.η i) (|Q.Ω i|) := by
 intro i Y Q; have ht:= (A.B.plan.rows N Vx hv).2.1; refine ⟨fun i j=> (ht i j).mono le_rfl (le_abs_self _),?_⟩
 have hp:= A.B.plan.all N Vx hv Wx; rw [←PriceCompiler.params_eq A.B.valid]; let x:=X.K.Ω i; have hv{S : Type}[Fintype S]{f:Matrix S S ℝ}(h:Numeric f (Q.η i) x): Numeric f (Q.η i) (|Q.Ω i|):= fun v=> ⟨(h v).1,(h v).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg (fun i _=> mul_self_nonneg (v i))))⟩
 exact ⟨hp.diagonalInv,hp.inverse,hp.roots,hp.starts,hp.same,hp.symmetric,hv hp.uniform.1,hv hp.uniform.2⟩
-- avoid included h above? unwanted m h param
variable {m' : ℕ→ℕ→ℝ}(hp:RankCovariance.ShapePort A.B.a A.B.M m')
include hp
lemma har : Extra.Iteration.Harmonic (A.B.M.towers N m):= by
 intro r s α β; rw [(hp.2 N m h).2]; exact harmonic_column (Next.Free.destination (E) N m) _ A.B.a.clock.kernel.penalty_pos (A.B.a.clock.adm m) r s α β
variable (hL:∀ x,R.Rise x ((D.L x).val:ℝ)) (hY:k+2≤ A.B.a.clock.J m)
include hL hY
lemma prayer (i:Age)(hi:i∈Age.scope (k+2)) : StateE.Kernel (θ Xz i) (θ Xy i) (Zx) (Zy) (w) C₁ C₀ (U):= by
 have he:=step_paid A.B.a m; let hx t:=R.shape k|>.pos t i; let hy:= R.shape k|>.use i Xz Xy he hi; obtain ⟨hq,hB⟩:= hL Xz Xy he k hY i hi
 have hx' : (A.B.M.towers N m).Deep (X.K.α Xz) (X.K.Ω Xz) 1:= by have ha:= A.B.plan.costs N m h; exact ⟨ha.1,ha.2.1,ha.2.2.1,fun l hl=> ha.2.2.2 l (by have h:= A.B.a.clock.adm (m+1); omega)⟩
 refine ⟨hx _,hx _,hB,fun a b => ((A.B.plan.rows N (m+1) h).2.2.2.2 a b).mono hy.1 (le_abs_self _), fun a b =>((A.B.plan.rows N m h.le).1 a b).mono hy.2 (le_abs_self _), ?_,?_⟩
 · apply (show ∀ (x y : Side)(T:Towers x)(hp:x=y)(b C:ℝ),T.Deep b C 1→ (show Towers y from hp ▸ T).Deep b C 1 from fun x y T h _ _ => (by subst x; exact id)) _ _ (A.B.M.towers N m) (PriceCompiler.block_eq A.B.valid m); exact WilsonStartup.Change.deep_mono _ hx' hy.1 (le_abs_self _)
 exact (show ∀ (x y : Side)(T:Towers x)(hp:x=y), Harmonic T→ Harmonic (show Towers y from hp ▸ T) from fun x y T h => (by subst x; exact id)) _ _ _ (PriceCompiler.block_eq A.B.valid m) (har A h hp)
local notation "I"=> Card D R Xz Xy (A.B.a.clock.adm (m+1)) k
structure Journey (i:I) : Prop where
    books : Plateau.Line.Books A (m:=m) (N:=N) i.self
    was : i.up=A.B.M.H N (m+1)
    now : i.down=A.B.M.H N m
    star : i.star=starBo A m N
include F
variable (H:Shop.Lodge D F.shape (fun _ i=> Shop.edgeW i) A.delay)
include H
lemma point (S:Layout G)(hv:∀ i∈ Age.scope (k+2), Quoted (S i) (θ Xz i) (authority k i D₀)): ∃ i:I, Journey R A (k:=k) (m:=m) (N:=N) i∧ i.extra=S:= by
 obtain ⟨u,hu⟩:=accounting A F (m:=m) (N:=N) h H; let hx:=strip_pay (m:=m) A h h; let hy:=strip_pay (m:=m) A h h.le
 refine ⟨⟨u,C₁,C₀,U,S,fun i hi=>?_,prayer R A h hp hL hY,(hx 1).1,(hy 1).1,?_,?_,fun n=> (hx n).2,fun n=> (hy n).2,fun n=> F.pledging.conducts.full N (m+1) n h,fun n=> F.pledging.conducts.full N m n h.le, ?_⟩, ⟨hu,rfl,rfl,rfl⟩,rfl⟩
 · rw [hu.fisc]; exact hv i hi
 · rw [hu.north]; exact A.B.support.links N (m+1) h
 · rw [hu.south]; exact A.B.support.links N m h.le
 rw [hu.north]; intro n; exact sweep A F h n -- defeq
end PlanV
end YM.AllOrder.Floe.Step
