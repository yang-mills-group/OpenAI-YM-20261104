import YM.QuadraticLocal.Tariff.Readings
import YM.QuadraticLocal.Rebirth.Pipe
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ) (hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Order.Join Comparison.RG02.Cumulants YM.Multi
open YM.Extra.Trajectories (connected)
-- projection polynomial table to ANY polar word by treating it as another axis; preserve θ component operators.Work.Frame.Param.Author.Engine.Volume
variable (r:ℕ)
local notation "Sr"=> (Replica u R)
open Comparison.RG02.Order Cumulants Next.SectorChange Bulk Assembly Precision Laurent
open Multi PertExtension.Series
open Exterior Tree
open scoped InnerProductSpace ContDiff
local notation "Θ"=> ( Replica u R )
set_option quotPrecheck false
variable (g : W→ℂ)
local notation "Φ"=> (Tariff.alg u R r g)
local notation "σ"=> ( Replica.sign u R g )
local notation "A"=> ( Replica.mouth u R g )
-- Gamma transform preserving formal valuation-lowered source power shape. Need kℓ old horizon coherence.User.Term.Fore Frame.
local notation "Z"=> Launch.Runtime.Memory.Height.Step.Area
local notation "ξ" i:max j:max=> (Replica.bill u R j)=i
variable (D : Bulk.Colors (Replica u R) G n) (pB: Multi.Hot R →ℕ)
local notation "Y"=> ( Tariff.chosen u R g D pB )
variable (hP:∀ (i:Multi.Hot R)(j:Multi.Hot (Replica u R)), Replica.bill u R j.val=i.val→ pB i =D.power j ) (hV: D.Standard)
local notation "Ht"=> ( Tariff.chamber u R r g )
open Integration.LocalFormal
local notation "ζ"=> ( Tariff.chosen u R g D pB )
variable {C:Family G}
variable (Y₀:Bulk.Chain C.path)
open Valence Moving Moving.Path Moving.Shift Comparison.RG02.Adjacent
open Earn
local notation "Wch"=> Stationary.arm G n 1
-- shift β calendar.State.Actor Tool: pre-Birth and lifted Post.Error tags.Sequence.Ph.Policy.Chart.P*. Motion commutes projection before any non-null.Primary.Cost invoice.E.Sh.
variable (u':UnitCost) (x:Stationary.Link G n) (s:R.Mode)(j:ℕ)(L:ℕ)
local notation "ζ₀" i:max p:max=> (fun x': Stationary.Link G n=> (Air.discharge D i (Stationary.arm G n 1 x')).part p)
local notation "ζ₁" i:max=> (fun x': Stationary.Link G n=> (Air.discharge Y i (Stationary.arm G n 1 x')).part s)
local notation "θ" t:max=> (u'.rating t)
local notation "φ'" p:max=> ( fun t:ℝ=> Adjacent.ages ( fun i=>ζ₀ i p ) 0 L t ( θ t ) x )

include hV hP
lemma soothe (i:ℕ)(p:(Replica u R).Mode): ContDiff ℝ ω (ζ₀ i p):= by
    unfold Air.discharge; by_cases h:p=( Replica u R ).quiet; · simp_rw [h,Multi.part_lit_quiet]; exact contDiff_const
    let j': Multi.Hot (Replica u R):=⟨p,(hot_iff_ne _).2 h⟩; simp_rw [show ∀ f,( Multi.lit (Replica u R) f ).part p=f j' from fun f=> Multi.part_lit _ j']; exact ( Adjacent.levelJet (hV.1.suppose_mark j').smooth _ ).smooth.comp (contDiff_const.prodMk ((Stationary.arm G n 1).toContinuousLinearMap.contDiff))
lemma weather (p:( Replica u R ).Mode): ContDiffAt ℝ ω (φ' p) 0:= by
   unfold ages; simp_rw [zpow_zero, Complex.ofReal_one, one_mul]; unfold Adjacent.cover;
   apply ContDiffAt.sum; intro i _; apply ContDiffAt.mul; · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiffAt_id.mul u'.smooth)).pow i
   let y t:= ( θ t )⁻¹; have hp: (fun t=> ( θ t )⁻¹) = (fun t=> ( θ t )^(-1:ℤ)):=by simp; -- maybe admits. can avoid via smooth.inv
   have he : ContDiffAt ℝ ω y 0:= by unfold y; rw [hp]; exact u'.spin (-1)
   exact ( ( soothe u R D pB hP hV i p ).contDiffAt.comp (0:ℝ) ( he.smul ( contDiffAt_const (c:=x) ) ) ) -- c keyword? p.Edit
local notation "Yₚ"=> (fun t:ℝ=> Adjacent.ages (fun i=> ζ₁ i) 0 L t ( θ t ) x)
lemma advise (t:ℝ)(d:ℝ) : Adjacent.ages (fun i=>ζ₁ i) 0 L t d x= ∑ p:(Replica u R).Mode,(if ϕ p=s then σ p*Adjacent.ages (fun i=>ζ₀ i p) 0 L t d x else 0):= by
   unfold Adjacent.ages Adjacent.cover; simp_rw [← Tariff.discharge u R g D pB hP hV, Replica.quota, zpow_zero, Complex.ofReal_one, one_mul, mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; split; next h=> apply sum_congr rfl; intro j _; ring
   next h=> simp_rw [mul_zero,sum_const_zero] -- split may s... first under sum implicit
lemma birth : Adjacent.born (fun i=>ζ₁ i) u' 0 L j x=∑ p:( Replica u R ).Mode,( if ϕ p=s then σ p * Adjacent.born (fun i=>ζ₀ i p) u' 0 L j x else 0 ):=by
    change Comparison.RG02.Moving.Path.motion (Yₚ) j= _; simp_rw [Tariff.advise u R g D pB hP hV x s L];
    let Ff(p:(Replica u R).Mode)(t:ℝ):= if ϕ p=s then σ p* (φ' p) t else 0; change Moving.Path.motion (fun t=>∑ p:( Replica u R ).Mode,Ff p t) j = _;
    have hp(p): ContDiffAt ℝ ω (Ff p) 0:= by unfold Ff; split; exact contDiffAt_const.mul ( Tariff.weather u R D pB hP hV u' x L p ); exact contDiffAt_const
    rw [Moving.Shift.msum _ Ff (fun i _=> hp i)]; refine sum_congr rfl fun i _=>?_ ; unfold Ff; split; next h=> exact Moving.Shift.mscale _ ( Tariff.weather u R D pB hP hV u' x L i )
    next h=>rw [ Moving.Shift.mconst ]; split <;> rfl
variable (D1: Bulk.Colors (Replica u R) G n)(hD: D1.Standard) (hP₁: ∀(i:Hot R)(p:Hot (Replica u R)), Replica.bill u R p.val=i.val → pB i=D1.power p)
local notation "Y1"=> ( Tariff.chosen u R g D1 pB )
include hD hP₁
lemma born (he:∀ p:(Replica u R).Mode,( Air.discharge D1 j (Stationary.arm G n 1 x) ).part p= Adjacent.born (fun i=> ζ₀ i p) u' 0 L j x): ( Air.discharge Y1 j (Stationary.arm G n 1 x) ).part s= Adjacent.born (fun i=> ζ₁ i ) u' 0 L j x:= by rw [← Tariff.discharge u R g D1 pB hP₁ hD, Replica.quota,birth u R g D pB hP hV u' x s j L]; simp_rw [he]
end YM.QuadraticLocal.Tariff
