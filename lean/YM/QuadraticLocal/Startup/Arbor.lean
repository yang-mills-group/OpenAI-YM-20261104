import YM.QuadraticLocal.Travel
import YM.QuadraticLocal.Germ.Scribe
/-!
# Installing off-mask flagged partners on the actual vacuum

 At FINAL spot of the two K mergers, already press-aligned to Actor.p. Uses second.Kiosk COST
 slack, obtained from procurement schedule. We don't hope the output K needs fewer flags
 following registration: purchase BEFORE cutting signatures. Can retain full nonlinear
 multipliers on any current torus.Touch and pool.Auto covers mega.Small. Publication estimates
 subsequently can use normalized full family using different flag.He.Is. Identity uses NO positivity
 on input/output vacuum densities; g depends on β at installment actual.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Wilson Lattice RG Marker Push Push.AbsoluteSums MeasureTheory
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X Y:Activities G n}
variable {F:Ovens.Code G n}{P:ℕ→ForcedAddress G n}
variable {α:Type*}{V ι:Type}[DecidableEq V]{R:Census V}{o:V→Site n}
variable {B s:ℕ}{a b f τ c k:ℝ}{w:V→ℝ} (hw:∀ i,0<w i)
namespace Hard
open Ac Corrected
-- predicate-free field-Extension (but reads.F) vacant scores.Transfer.Pool. No Current K needed. Require geometry at forced address.
structure Rent (P:ℕ→ForcedAddress G n)(F:Ovens.Code G n)(p:BudgetPoint) (a f:ℝ):Prop where
    sym i : GaugeInvariant (F i)
    meas i : Measurable (F i)
    permit i U : F i U≠0→ (P i).eligible p.threshold U
    own i : UsesFinal p.threshold (P i).support (F i)
    earns : ∃ g:ℕ→ℝ,(∀ i,0 ≤ g i) ∧ (∀ i U, ‖F i U‖ ≤ g i) ∧ Hit (fun i=>(P i).support) p.B g a f
variable (h:Rent P F p a f)
include h
/-- Only scalar rent. Exact Hero on all finite trajectories. -/
def rent (t: Rent P F p a f): Hard α p P F o R:=
   { hard:=fun _ i U=>Poly.bead R (F i U)
     locality:= fun _ i=> by refine ⟨fun v U=> congr_arg (fun x:ℝ=> Poly.bead R x) (t.sym i v U), (GridRenewal.Rain.lit R).measurable.comp (Complex.continuous_ofReal.measurable.comp (t.meas i)),fun u v h hb=> congr_arg (fun x:ℝ=> Poly.bead R x) (t.own i u v h hb),fun U q h v hv=>?_⟩; exfalso; apply h; change (Poly.send R.quiet _).part q=_; rw [Poly.part_send,if_neg (show q≠R.quiet from fun h=> Finset.notMem_empty v (show v∈R.quiet.val from h ▸ hv))] -- missing subst
     charged:= fun _ i U h=> t.permit i U fun hn=>h (by rw [hn]; simp)
     quiet:=fun _ i U=> by change (Poly.send R.quiet _).part R.quiet=_; simp }
omit h in
lemma leasing {F :ℕ→ ForcedAddress G n} {P: Ovens.Code G n} (t: Rent F P p a b): (rent (α:=α) (o:=o) (R:=R) t).Paid w p.B a b:= by
   obtain ⟨f,h,hP,hH⟩:= t.earns; refine ⟨fun i=> Poly.send R.quiet (f i), fun i x U q=> ?_, ?_⟩
   · by_cases he:q= R.quiet; subst q; · simp only [rent,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk, OneHom.coe_mk, Poly.part_send, if_true]; exact ⟨by simpa using hP i U,rfl⟩
     unfold rent; dsimp only; change ‖(Poly.send R.quiet _).part q‖≤_∧_; simp [he]
   simp_rw [Poly.solo,Poly.quiet_toll,Complex.norm_real,Real.norm_of_nonneg (h _),one_mul]; exact hH
omit h
lemma rentValid (H:X.ForcedFamily p)(h:X.KBound p b): Rent X.forced X.K p p.supportExponent b:= by
   obtain ⟨f,h,hF⟩:=h; refine ⟨H.sym,H.meas,H.permit,H.reads,f,(fun i=>(h i).1),(fun i =>(h i).2),?_⟩; intro i; convert hF i using 1; ext j; unfold BudgetPoint.mass; split<;>ring
-- `rent` recover from ANY paid Family even if Mark.N not zero
lemma transfer (K0:Hard α p P F o R) (a) (T:α) (h:K0.Paid w p.B a b) (hw:∀ i, 0<w i): Rent P F p a b:=by
   obtain ⟨f,hp,hF⟩:=h.wages; let h i := K0.locality T i
   have he i U : ( (K0.hard T i U).part R.quiet).re= F i U:=by rw [K0.quiet]; rfl
   have hv (i U): F i U=( (K0.hard T i U).part R.quiet).re:= Eq.symm (he i U)
   refine ⟨fun i v U=>?_,fun i=>?_,fun i U hn=> ?_,fun i u v hi ht=>?_, fun i=> Poly.price w (f i),fun i=> Poly.nonnegative hw _,fun i U=>?_, hF⟩
   · rw [hv i (Lattice.gauge v U),hv i U,(h i).gauge]
   · rw [funext (hv i)]; exact Complex.continuous_re.measurable.comp ((Poly.part_cont _).measurable.comp (h i).borel)
   · exact K0.charged T i U (fun h=> hn (by rw [hv,h]; rfl) )
   · rw [hv i u,hv i v,(h i).reads u v hi ht]
   apply le_trans ((le_of_eq ?_).trans (Poly.member hw R.quiet (K0.hard T i U))) ((hp i T U).reprice _ hw)
   rw [Poly.quiet_toll,K0.quiet,one_mul,Complex.norm_real]
-- K output slack possession independently of stage path or vacuum.Stash
structure Install (X:Activities G n)(p:BudgetPoint)(k c:ℝ):Prop where
    room : ∃ U:Activities G n,∃ e:ℝ,Nonempty (Kiosk.Second p U X e k p.supportExponent c) ∧ Rent U.forced U.K p (p.supportExponent+1) e
end Hard
open Corrected Hard Kiosk Canopy Ovens Ovens.Pipes
open Affinity Fusion Fusion.Attached
variable [Fintype V]
local notation "R!"=> Poly R
lemma curtains {n : Side} {X Y:Activities G n}(hx:X.forced=Y.forced)(K:ℕ→ Config G n→ Poly R)(U:Config G n): packet X p K U=packet Y p K U:=by
   funext i; unfold packet; rw [show X.admissible p U i= Y.admissible p U i from by unfold Activities.admissible; rw [hx]]
-- other hidden implicit G.P overshadow rebaseremove
variable (H:Kiosk.Second p X Y b f a c) (hx:Rent X.forced X.K p (a+1) b)
variable (T:ShiftRows α ι G p o R)
local notation "R₀"=> rent (R:=R) (α:=α) (o:=o) hx
set_option quotPrecheck false
open RG3 Ink Progress.DirectedRecipe
namespace Hard.Rent
local notation "Λ"=> Kiosk.Second.canopy R₀ T H
variable (ha:0≤a)
variable [Countable ι]
variable (ht:T.Budget w p.B (a+1) c)
open GridRenewal.Rain
local notation "P!"=> (H.skeleton.pours H.tap)
include hx ht ha hw
lemma instals : (Λ).Paid w p.B a f ∧ ∀ (t:α) (U:Config G n), HasSum (packet Y p ((Λ).hard t) U) ((↑(Y.gas p U):ℂ) • Poly.pass (T.log t U)):=by --- fix XK=(↑ Y.gas)
   let R':=Kiosk.shape H.oldP H.oldV R₀; let hx':= Kiosk.turned H.oldP H.oldV R₀ (Hard.leasing (w:=w) hx); refine ⟨Kiosk.turned H.projection.symm H.keeps.symm _ (T.budgets H.softens R' hw ha H.softPaid hx' ht H.funds),?_⟩
   intro t U
   have hpk : HasSum (packet Y p ((Λ).hard t) U)
       ((Real.exp (∑' i,(Rack.widen H.skeleton H.tap).logarithm i U):ℂ) • ((∑' i, packet X p ((R₀).hard t) U i)* cyclone (T.log t U))):=by
       rw [curtains (Y:=fused (folio G n) p (Rack.widen H.skeleton H.tap)) H.projection,curtains (Y:=P!) H.oldP]; exact T.posterSum H.softens R' hw ha H.softPaid hx' ht H.funds t U -- curtains eq mismatch?
   let Φ:= (↑(Real.exp (∑' i,(Rack.widen H.skeleton H.tap).logarithm i U)):ℂ)
   have hh:= Hard.packet_summing R₀ (Hard.leasing (w:=w) hx) (add_nonneg ha zero_le_one) hw t U
   have hV:R'.hard t=(R₀).hard t:=rfl; let F i:= X.gasOccurrence p i U
   have hS: ∑' i,packet X p ((R₀).hard t) U i= Poly.bead R (X.gas p U):= by
       have hU i : packet X p ((R₀).hard t) U i= Poly.bead R (F i):=by
          unfold packet F Activities.gasOccurrence; split; next=> rw [Complex.ofReal_prod,map_prod]; rfl
          next=> simp
       -- use `share` or continuous hom in tsum ℝ. here pointwise continuous and abs.
       ext q; by_cases he:q=R.quiet; subst q; · exact (Hard.packet_of_quiet R₀ t U hh).trans (Poly.part_send ..|>.trans (if_pos rfl)).symm
       rw [Poly.share hh]; simp_rw [hU]; change (∑' i,(Poly.send R.quiet _).part q) = (Poly.send R.quiet _).part q; simp_rw [Poly.part_send,if_neg he,tsum_zero]
   have ho: (T.log t U).part R.quiet=0:=by unfold ShiftRows.log; rw [Poly.share (T.earnings ht hw (add_nonneg ha zero_le_one) t U)]; simp_rw [T.skip]; exact tsum_zero
   have hZ: Φ*(X.gas p U)=Y.gas p U:=by
      have he:= Hard.packet_of_quiet Λ t U hpk.summable; rw [hpk.tsum_eq, hS,GridRenewal.Rain.passes _ ho,Poly.part_smul, Poly.quiet_mul,Poly.pass_part _ ho] at he; exact (show Φ*(↑(X.gas p U):ℂ) = _ from by simpa only [mul_one,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.part_send,if_true] using he)
   rw [hS,GridRenewal.Rain.passes _ ho, Poly.product_bead,smul_smul,hZ] at hpk; exact hpk
end Hard.Rent
end YM.QuadraticLocal
