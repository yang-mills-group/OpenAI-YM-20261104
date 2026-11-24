import YM.Comparison.RG02.Symphony.Cleat
import YM.Push.LOOP_COEFFICIENT.KineticLines
/-! # Signature of the flat homogeneous potential two-leg action
On any polynomial Sheet with actual flow, before any RG08 plane/cofinal operations. Use
REAL signed spin law of the Wilson prescription. When applying to that
step and history see `earned` and `accepted` for minimal premises. Use **action** sign, i.e. pull
from `Orbit.ground` which is the logarithm incl - unit base THEN take negative-real.
No extra factorial here. No cancellation in represented vocab or curvature lifting nor any
approximation estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c: Side} {m : ℕ→ℤ} {r k : ℕ}
local notation "X"=> fieldDir G c 1
local notation "K"=> BondKey G c
local notation "Ξ"=> chartEquiv G c
namespace Clarity
variable (p:fieldDir G c 1→ℂ)
def real (p:fieldDir G c 1→ℂ):= (⇑(-Complex.reCLM)) ∘ p
def full (p:fieldDir G c 1→ℂ) := real p ∘ (Ξ).toContinuousLinearMap
def value (p:fieldDir G c 1→ℂ) : Matrix (BondKey G c) (BondKey G c) ℝ := bilinearAt (full p) 0
variable {p} (he:ContDiffAt ℝ ω p 0)
local notation "V"=> Clarity.value p
include he
lemma known : ContDiffAt ℝ ω (real p) 0:= by unfold real; exact (-Complex.reCLM).contDiff.contDiffAt.comp 0 he
lemma onGrid: ContDiffAt ℝ ω (full p) 0:= by unfold full; exact ((Ξ).map_zero.symm ▸ known he:ContDiffAt ℝ ω (real p) (Ξ 0)).comp (f:=(Ξ).toContinuousLinearMap) _ ((Ξ).contDiff.contDiffAt)
lemma reads (x y: BondKey G c → ℝ): x ⬝ᵥ (value p *ᵥ y) = - Complex.re ((iteratedFDeriv ℝ 2 p 0) ![Ξ x,Ξ y]) := by
    rw [value,bilinearAt_dotProduct, ← bend_apply, full,bend_linear _ (known he),bend_apply,real, (-Complex.reCLM).iteratedFDeriv_comp_left he le_top]; rfl
lemma congruence (S : X→L[ℝ]X) (M: Matrix (BondKey G c) (BondKey G c) ℝ) (hp: ∀ v, p (S v)=p v) (hv: ∀ z, Ξ (M*ᵥ z)= S (Ξ z)): M.transpose*value p * M = value p:= by
    unfold value; refine of_bend_congruence M fun x y=> ?_; unfold full; rw [bend_linear _ (known he),bend_linear _ (known he)];
    change bend (real p) _ (Ξ _) (Ξ _) = bend (real p) _ (Ξ x) (Ξ y)
    rw [hv,hv, ← bend_linear S (known he), show real p∘ S=real p from funext fun x=> by exact congr_arg (⇑(-Complex.reCLM)) (hp x)]
lemma full_spin (hS : ∀ s:Signed,p ∘ shifts s 0=p)(s:Signed) : let L:= linkSpin s (1:Config G c); L.transpose*value p * L=value p := by
   intro l; refine congruence he _ _ (congr_fun (hS s)) (fun z=>?_); rw [show l=linkSpin _ _ from rfl,chart_pulled]; symm; funext k; unfold shifts Bid.pulled; rw [ContinuousLinearMap.pi_apply]; dsimp only; split <;> rfl
lemma color (hS:∀ z:G.El, p ∘ CubicMatch.recolor z 1=p)(z:G.El) : let L:= linkAdj (constantGauge (n:=c) z); L.transpose*value p * L=value p := by
    intro l; refine congruence he _ _ (congr_fun (hS z)) (fun v=> ?_); unfold l linkAdj; funext x; rcases x with ⟨x,i⟩; obtain ⟨i,rfl⟩:= axisEquiv.surjective i; change Ξ _ (x,coord i)= G.adjoint z ((Ξ _) (x,coord i)); rw [chartEquiv_apply,paint_adjoints,chartEquiv_apply]; rfl
omit he in
private lemma gradient (x: SiteKey G c →ℝ) : Ξ (R_g (1:Config G c) *ᵥ x)= dColor G c 0 (fun z=> -paint G _ x z.1):= by
    rw [R_g, LinearMap.toMatrix'_mulVec]; funext i; rcases i with ⟨a,j⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective j; rw [coord_map, chartEquiv_apply, paint_brace]; ext q; unfold dColor; rw [Pi.one_apply,G.adjoint_one]; change x _ - x _ = (d 0 c *ᵥ _) (_,_); rw [d_sites]; change x _-x _ = - x _- - x _; abel
lemma horizontal (h: ∀ (u: fieldDir G c 0)(v: fieldDir G c 1), iteratedFDeriv ℝ 2 p 0 ![dColor _ _ _ u,v]=0): value p* R_g (1:Config G c)=0 := by
    apply pairing_ext (Y:=0); intro y x; rw [← mulVec_mulVec, reads he, gradient]; let w:fieldDir G c 0:= fun z=> -paint G _ x z.1; rw [Matrix.zero_mulVec,dotProduct_zero, he.isSymmSndFDerivAt_of_omega.iteratedFDeriv_cons, h]; simp
omit he
structure Body (p:fieldDir G c 1→ℂ):Prop where
    paired: (value p).IsSymm
    horiz: value p* R_g (1:Config G c)=0
    spin (a:Signed) : let L:= linkSpin a (1:Config G c); L.transpose*value p * L=value p
    color (u:G.El) : let L:=linkAdj (constantGauge (n:=c) u); L.transpose* value p * L = value p

lemma earned {q:Display (fieldDir G c 1)} (hq:Sheet r q) (hC:Charge r m q)(hk:k≤r)(hG:G.Simple)(h:∀s:Signed,q k ∘ shifts s 0 = q k) : Body (q k):= by
   let he := (hq.known k hk).contDiffAt (x:=0); exact ⟨of_bend_symm (onGrid he), horizontal he (fun _ _=> Cleat.groove hq hC hk hG ..), full_spin he h, color he (fun z=>funext fun x=> hq.color x hk z)⟩
lemma accepted {n:ℕ→Side} {p:∀i, fieldDir G (n i) 1→ℂ}{s : Momentum→ Matrix (Axes G) (Axes G) ℂ}(hn:Expands n)(H: ∀ i,Body (p i))(hp: LinkMirror (fun i=> value (p i)) s): Signature G true s := by exact ⟨fun _ hh=>hp.symmetric hn hh (fun i=>(H i).paired),fun _ hh=>hp.hermitian hn hh (fun i=>(H i).paired),fun _ hh=>hp.ward hn hh (fun i=>(H i).horiz),fun a _ _ hh=>hp.spin hn hh a hp (fun i=>(H i).spin a),fun _ hh=>hp.color hn hh (fun i z=>(H i).color z) ⟩
end Clarity
end YM.Comparison.RG02.Symphony
