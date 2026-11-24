import YM.AllOrder.Floe.Voyage
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
abbrev starBo (m N:ℕ) : Towers (D.L (A.B.a.clock.J (m+1))):= (PriceCompiler.block_eq A.B.valid m) ▸ A.B.M.towers N m
local notation "ℒ"=> (A.B.a.S.block m)
variable (h:m<N)
section patch
variable {Q Q':Bed} (v:PathData G) (D' : Clip)
def Agenda {c f:Side} (S:StepData c f)(L:Towers S.patch.L):Prop:= Towers.Diagonal S Q Q' L ∧ ∀ t:Forest S.ratio,∃ ρ, Critical (S:=S) t D' v ρ ∧ Guessed (S:=S) t (installed S.ratio L.A0) ρ
lemma agenda_shift {c f:Side} (S S':StepData c f) (L:Towers S.patch.L) (ht: S'=S) (ha: Agenda (Q:=Q) (Q':=Q') v D' S L): Agenda (Q:=Q) (Q':=Q') v D' S' (ht.symm ▸ L):= by subst S; exact ha
lemma agenda_eq {c f:Side} (S S':StepData c f)(L:Towers S.patch.L) (L':Towers S'.patch.L) (hP:S'.patch=S.patch)(hK:S'.kernel=S.kernel)(hk:(congr_arg Patch.L hP) ▸ L'=L) (h:Agenda (Q:=Q) (Q':=Q') v D' S L): Agenda (Q:=Q) (Q':=Q') v D' S' L':= by
 have he:S'=S:= by cases S; cases S'; congr <;> assumption -- patch maybe ext. After subst
 subst S'; change L'=L at hk; subst L'; exact h
end patch
local notation "T'"=> starBo A m N
include h
lemma crossed (u:ℕ) : let S:=A.B.a.clock.op m u; let L := T'; ∀ (S':StepData (A.B.a.S.side m u) (A.B.a.S.side (m+1) u)) (hP:S'.patch=P)(hK:S'.kernel= X.p.kernel), Agenda (Q:=C₁) (Q':=C₀) W ((X.p.profile Xz).clip) S' ((congr_arg Patch.L hP).symm ▸ L):= by
 intro S L S' hP hK; let Q:= P; have he: S.patch=P:= Plateau.Line.patch_here A (m:=m) (A.B.a.S.oneStep m u).exact_size
 have hf : S'.patch=S.patch:= hP.trans he.symm; apply agenda_eq _ _ S S' (A.B.M.towers N m) _ hf (hK.trans A.B.valid.kernel.symm) ?_ ⟨A.B.plan.crossings _ _ _ h,(fun F=>⟨A.B.kin.stationary N m u F,?_⟩)⟩
 all_goals first | (rw [← PriceCompiler.params_eq A.B.valid]; exact A.B.support.critical N m u h _) | (refine eq_of_heq ?_; apply HEq.trans (eqRec_heq (φ:= Precision.Towers) ..); apply HEq.trans (eqRec_heq (φ:= Precision.Towers) ..); exact (eqRec_heq (φ:= Precision.Towers) (PriceCompiler.block_eq A.B.valid m) (A.B.M.towers N m)))
lemma crossed' (u:ℕ) : let c:=A.B.a.S.side m u; Agenda (Q:=C₁) (Q':=C₀) W ((X.p.profile Xz).clip) (dock P K c) T':= by
 intro c; let f:= A.B.a.S.side (m+1) u; have hx : Progress.ClassicalKin.Tent.below P c=f:= by
    apply Subtype.ext; show c.val*(D.L Xz).val=(A.B.a.S.side (m+1) u).val; rw [← PriceCompiler.block_eq A.B.valid m]; exact (A.B.a.S.oneStep m u).exact_size.symm
 have hA(f' : Side)(hh:f'=f): ∀ (S':StepData c f') (hP:S'.patch=P) (hK:S'.kernel=K), Agenda (Q:=C₁) (Q':=C₀) W V S' ((congr_arg Patch.L hP).symm ▸ T'):= by subst f'; exact crossed A h u
 exact hA _ hx _ rfl rfl
include F
lemma sweep (n:Side): ContinuousLife (fun l:Side=> Ad G P K l ∧ Agenda (Q:=C₁) (Q':=C₀) W V (dock P K l) T') n:= by
 let a(l:ℕ):= A.B.a.S.side m l; have hv:= UVNext.PricedKernels.Echo.schedule_sides (E).S m; obtain ⟨v,hv'⟩:=dock_larger P K (X.p.has (P)); choose p hp hP using fun l=> F.floor n l; have hx:Tendsto p atTop atTop:= tendsto_atTop_mono (f:=id) hp tendsto_id; let b'(i:ℕ):=a (p i); have hu:=hv.comp hx; obtain ⟨f,hpt⟩:=Filter.eventually_atTop.mp (hu.eventually_ge_atTop v); let b i:= b' (i+f); choose d hd using fun i:ℕ => (show ∃ k:ℕ,(b i).val=n.val*k from (show n.val ∣ (b i).val from dvd_mul_of_dvd_left (hP (i+f)) _)); refine ⟨b,fun i=> (d i)^4, hu.comp (show Tendsto (fun i:ℕ=>i+f) atTop atTop from tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id), fun i=>?_,fun i=>⟨⟨Macrame.normal ⟨_,hd i⟩ (hd i)⟩,hv' _ (hpt _ (Nat.le_add_left ..)), crossed' A h (p (i+f))⟩⟩
 apply pow_pos; have he:0<n.val * d i:= (hd i) ▸ (b i).pos; by_contra! h; rw [Nat.le_zero.mp h] at he; omega
end PlanV
end YM.AllOrder.Floe.Step
