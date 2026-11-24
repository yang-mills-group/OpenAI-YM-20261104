import YM.RGComparison.Core16.Lam.Under
import YM.RGComparison.Core16.Spool.Proof
/-!
# STEP Hessian = actual shared-tag posterior covariance & field score

Use before turn on Fitted iteration. Here exact primitive-costs in compact Hess.W
calculus **only after volume**. Obtain Asp moments beforehand via Lens estimator; no exponential assertion after pricing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι :Type}[Fintype ι]

-- keep trace conventions. use G.chord = ‖X-1‖/sqrt repDim at group el. CREDIT formal normalization θ=M. Field link argument Geometric QColor real orientation. Work even if K vs hatted schedule heights differ, paid individually at g.

def arm (K:KernelChoices)(p:G.Color× G.Mat):= K.penalty*(‖G.mat (G.lieExp p.1)*p.2-1‖^2/(Real.sqrt G.repDim)^2/2)
lemma installs (K:KernelChoices)(x y:G.El)(v:G.Color)(h:x=G.lieExp v): K.penalty*G.price (x*y)= arm K (v,G.mat y):=by
     unfold arm; rw [h]; rw [(show (G.mat (G.lieExp v)* G.mat y)=G.mat (G.lieExp v*y) from rfl), ←div_pow]; change _= _ * (G.chord _^2 /2); rw [G.chord_price]; ring
attribute [local instance] Gauge.frobInner
lemma arm_hot (K:KernelChoices): ContDiff ℝ ω (arm (G:=G) K) :=
     contDiff_const.mul ((((contDiff_norm_sq ℝ).comp (((G.exp_jet.comp contDiff_fst).mul contDiff_snd).sub contDiff_const)).div_const _).div_const _)

abbrev News (G:Gauge)(c:Side):= (ℝ × (ℝ × (Edge (Site c)→ G.Mat)))

variable {c f: Side} (S : StepData c f) (T:Forest S.ratio)(t:S.Choices)

def around (u:Sky G T.Free): Edge (Site c)→ G.Mat:=fun i=> G.mat ((S.prediction (T.drape u) t i)⁻¹)

def fire (u:Sky G T.Free): News G c:= (S.likelihood (T.drape u) t, Wilson.energy (T.drape u), around S T t u)

def stature (u: Directions G c) : Config G c:= fun i=> G.lieExp (u i)
@[simp] lemma statue : stature (0: Directions G c)=1:= funext fun _=>G.mat_lieExp_zero

def tax (p: News G c)(u:Directions G c):= p.2.1+∑ i, arm S.kernel (u i,p.2.2 i)
lemma tax_hot : ContDiff ℝ ω (fun u: Directions G c × News G c=> tax S u.2 u.1):= ContDiff.add (contDiff_fst.comp (contDiff_snd.comp (f:=Prod.snd) contDiff_snd)) (ContDiff.sum (f:=fun i (u:Directions G c× News G c)=> arm S.kernel (u.1 i,u.2.2.2 i)) (s:=univ) fun i _=> (arm_hot S.kernel).comp (((contDiff_apply ℝ G.Color i).comp contDiff_fst).prodMk ((contDiff_apply ℝ G.Mat i).comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))))) -- signature

def leaf (g:ℝ)(p:News G c)(u:Directions G c):ℝ:=p.1*Real.exp (-(g⁻¹^2)*tax S p u)

def bonnet (g:ℝ) (u:Directions G c)(x:Sky G T.Free):= leaf S g (fire S T t x) u
lemma flavor (g:ℝ) : ContDiff ℝ ∞ (fun u: Directions G c × News G c => leaf S g u.2 u.1) := ((contDiff_fst.comp (f:=Prod.snd) contDiff_snd).mul (contDiff_const.mul (tax_hot (G:=G) S)).exp).of_le le_top
lemma leaflet (g:ℝ) (u:Directions G c)(x:Sky G T.Free):
     bonnet S T t g u x= S.likelihood (T.drape x) t * (Hut.seam S T (stature u)).cash t g x:=by
    rw [Base.cash,Hut.action_eq]; unfold bonnet leaf; congr 2
    unfold tagEnergy noiseEnergy; rw [div_eq_inv_mul,inv_pow, tax]; simp_rw [show ∀ i:Edge (Site c), arm S.kernel (u i, (fire S T t x).2.2 i)=linkEnergy S ((stature u) i*(S.prediction (T.drape x) t i)⁻¹) from fun i=> (installs S.kernel (stature u i) ((S.prediction (T.drape x) t i)⁻¹) (u i) rfl).symm]; change -(g^2)⁻¹*_= (g^2)⁻¹ * -_; dsimp only [fire]; ring
lemma ceremony (g:ℝ)(u:Directions G c)(x : Sky G T.Free): (Hut.seam S T (stature u)).output g x= ∑ t, bonnet S T t g u x:=sum_congr rfl fun i _=> (leaflet S T i g u x).symm

variable (h:S.patch.Branches S.kernel G)
scoped instance (G:Gauge) : MeasurableSpace G.Mat:= borel _
scoped instance (G:Gauge) : BorelSpace G.Mat:= ⟨rfl⟩
scoped instance (G:Gauge) : SecondCountableTopology G.Mat:= inferInstanceAs (SecondCountableTopology (Fin G.repDim→ Fin G.repDim→ ℂ))
scoped instance (G:Gauge) : TopologicalSpace.PseudoMetrizableSpace G.Mat := inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin G.repDim→ Fin G.repDim→ ℂ))
include h
lemma huts : ∃ K:Set (News G c), IsCompact K ∧ (∀x,fire S T t x∈ K) ∧ Measurable (fire (G:=G) S T t):= by
     let M (y:Config G c):= fun i=> G.mat ((y i)⁻¹); have eM : Continuous M:=by unfold M; fun_prop
     have he: Continuous (energy ∘ (T.drape (G:=G))):= by fun_prop
     refine ⟨(Set.Icc (0:ℝ) 1)×ˢ(Set.range (energy ∘ T.drape) ×ˢ Set.range M), isCompact_Icc.prod ((isCompact_range he).prod (isCompact_range eM)),fun x=>⟨?_,⟨x,rfl⟩,?_⟩,?_⟩
     · let X:= (T.drape x); exact ⟨S.likelihood_pos X t,(S.chosen h X) ▸ (Finset.single_le_sum (f:=S.likelihood X) (fun i _=> S.likelihood_pos X i) (mem_univ t))⟩
     · exact ⟨S.prediction (T.drape x) t,rfl⟩
     exact ((S.likelihood_meas h t).comp T.continuous_drape.measurable).prodMk (he.measurable.prodMk (eM.measurable.comp ((S.prediction_meas h t).comp T.continuous_drape.measurable)))

-- Read out vacuum (full Markov); not omitting prefactor
local notation "Y" => Directions G c
local notation "μ"=> skillet G T.Free

def reel (g:ℝ) (F:News G c→ℝ) :ℝ:= ∫ x, leaf S g (fire S T t x) 0 * F (fire S T t x) ∂ skillet G T.Free

def collects (g:ℝ)(u:Directions G c):ℝ:= ∑ t:S.Choices,∫ x, bonnet S T t g u x∂skillet G T.Free

lemma income (g:ℝ)(u:Directions G c): S.push (g⁻¹^2) (bare (g⁻¹^2)) (stature u)= Next.Fluctuations.Sector.prefactor S G (g⁻¹^2) * collects S T g u := by
    rw [T.pushing (S.isKernel h _) _ _ (fun k x=> bare_gauge ..) (bare_integrable _) (fun k U=> S.covary h k _ U _),inv_pow,collects, ← integral_finsetSum univ]; swap
    · intro t _; obtain ⟨K,hK,hp,hF⟩:= huts S T t h; exact addition hF.aestronglyMeasurable hK hp (flavor _ g) u
    rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with x; rw [← ceremony]; exact Hut.bill ..
end YM.RGComparison.Core16.Lam
