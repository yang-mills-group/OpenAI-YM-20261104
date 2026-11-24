import YM.Frontier.Tuning.ComplexVertex
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Quires
/-!
# Same angular stencil at a held real argument, for ordinary AND log-only moments

β reference R.beta only chooses units of Z. Complexifying the coefficients of THIS
algebraic expression, not clearing guards on coarse evaluations. Useful on the
`Vine.vary` and `Flux.rhythm` paths. The input functions here replace regular numerical
terms at their individual indices and forced terms at their own indices. Bounds and
analyticity in any function norm are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.Held
open Filter Function Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel Bid SliceRows Control Window Census Mask Pulse Itinerary Coat
open Blaze Silica Scroll Vine Polar Coat Raw PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F) (R R': Rep G f) (I : Config G f) (u:Directions G f) (z:Air f G) (O:ChartRatio G)
variable (a B W:ℝ) (k:Finset ℕ) (τ:ℂ)
abbrev Payload (G : Gauge) (n : Side) := ComplexVertex.Payload G n

def comboLog (e : Payload G f) (i : LogIndex c f): ℂ:= match i with
  | Sum.inl (.inl j)=> -ComplexVertex.hiddenC R.p.threshold (R.activities.reg j).support (e j) I * X.enforce (2*a) u (X.plaza (space T 0 X.B R (.inl j)))
  | _ => (if flips c f i then τ/R.beta else 1) * logMoment X a R O u I z i


def penGain (P : Stores S) : ℂ := Complex.exp ((τ-R.beta)*(-(chalky X u I P+crispy X P):ℝ) + (X.pens P).card * (ComplexVertex.logMass O R.beta-ComplexVertex.logMass O τ))

def emberC (l : ℕ) (e h : Payload G f) : Head S→ℂ := Sum.elim
    (fun P : Stores S=> if Packets.connected S l X.B P then penGain X R I u O τ P * stock X a R W O u I k P else 0)
    (Sum.elim (fun j=>h j I * X.enforce (2*a) u (X.plaza (forcedFoot S.ratio 0 X.B R j))) (Sum.elim (fun i=>Complex.exp (comboLog X R I u z O a τ e i)-1) (fun i=> ↑(Polar.sprinkle X a R W u I k i))))

def floatC (l : ℕ) (e h : Payload G f) (p : Molecule S) := let w:= worldZ X R.beta z; ∏ i∈p,emberC X R (X.input w) w z O a W k τ l e h i

lemma log_real {e : Payload G f} (P:Facing R R') (he: ∀ j V,e j V=R'.activities.E j V) (i : LogIndex c f) :
    comboLog X R I u z O a (R'.beta:ℂ) e i = (logMoment X a R' O u I (low R R' • z) i:ℂ):= by
   classical
   by_cases hk: oldVac _ _ i
   · have h : R'.beta/R.beta=low R R'^2:=by rw [← pledge P]; field_simp [P.pos.ne']
     rcases i with (j|i)|i
     · exact absurd (rfl:(Sum.inl (.inl j):LogIndex c f)=Sum.inl (.inl j)) (hk j)
     all_goals rw [comboLog, flicker a P O X z u I _ hk]; rw [Complex.ofReal_mul]; apply _root_.congrArg (fun v:ℂ=>v*Complex.ofReal _); split_ifs; rw [← h]; norm_cast; norm_num
     all_goals exact hk
   unfold oldVac at hk; push Not at hk; obtain ⟨j,rfl⟩:=hk
   unfold comboLog; dsimp only
   unfold logMoment frost nest Activities.regularOccurrence
   rw [P.params,P.reg, ComplexVertex.hiddenC_real (he j)]; unfold Raw.space regularFoot; rw [P.reg]; simp only [Sum.elim]; push_cast; rfl

lemma penGain_real (P:Facing R R') (q:Stores S)(hO:0<O.scale) : penGain X R I u O (R'.beta:ℂ) q = (Real.exp (-(R'.beta-R.beta)*(chalky X u I q+crispy X q)-(X.pens q).card*(Real.log (measure_g O R'.beta)-Real.log (measure_g O R.beta))):ℂ) := by
    rw [penGain,ComplexVertex.mass_real hO P.pos, ComplexVertex.mass_real hO P.pos',Complex.ofReal_exp]; congr 1; push_cast; ring
set_option maxHeartbeats 650000 in
lemma ember_real {e f' : Payload G f} (P:Facing R R') (he:∀ j V,e j V=R'.activities.E j V) (hf:∀ j V,f' j V=R'.activities.K j V) (hO:0<O.scale) (l:ℕ) (i:Head S):
    emberC X R I u z O a W k (R'.beta:ℂ) l e f' i = (ember X a R' W O u I (low R R' • z) k l i:ℂ):=by
   rcases i with A|j|i|i
   · dsimp only [emberC,ember,Sum.elim]; split_ifs
     · rw [penGain_real X R R' I u O P _ hO, stockMoon a W P O X k u I _]; push_cast; exact mul_comm .. -- order?
     exact Complex.ofReal_zero.symm
   · change f' j I * (X.enforce (2*a) u (X.plaza (forcedFoot S.ratio 0 X.B R j)):ℝ) = ((sheath X a R' u I j:ℝ):ℂ); dsimp only [sheath]; rw [hf j,Complex.ofReal_mul]; apply _root_.congrArg (fun i=> Complex.ofReal _* Complex.ofReal (X.enforce (2*a) u (X.plaza i))); unfold forcedFoot; rw [P.forced]
   · dsimp only [emberC,ember,Sum.elim]; rw [log_real X R R' I u z O a P he]; push_cast;rfl
   · exact congr_arg Complex.ofReal (alarmWhistle a W P X k _ _ i)

lemma float_real {e f' : Payload G f} (P:Facing R R') (he:∀ j V,e j V=R'.activities.E j V) (hf:∀ j V,f' j V=R'.activities.K j V) (hO:0<O.scale) (l:ℕ) (i:Molecule S):
    floatC X R z O a W k (R'.beta:ℂ) l e f' i = (floating X a R' W O (low R R' • z) k l i:ℂ):= by
   change (∏ j∈i, emberC _ _ _ _ _ _ _ _ _ _ _ _ _ j) = Complex.ofReal _; rw [floating, moving P,Complex.ofReal_prod]; apply Finset.prod_congr rfl; exact fun j _=> ember_real X R R' _ _ z O a W k P he hf hO l j
lemma clutch_scale {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {j:ℕ}{d:ℝ}{y:E} (P:Facing R R') {V:E→ Config G c}{U:E→Directions G f}{g:E→Air f G}(h:Clutch X z a R.beta d y j V U g): Clutch X (low R R' • z) a R'.beta d y j V U (fun i=>low R R' • g i) :=by
   -- improve return type; should E Type only
   refine ⟨h.atV,P.pos',congr_arg _ h.birth,h.pulse,fun i=>?_,h.price,?_,?_⟩
   · rw [moving P]; exact h.moving i
   · rw [moving P]; exact h.bud
   rw [moving P]; exact h.patch

def traitE (R A: RG.Rep G f)(v s : ℂ) : Payload G f:= fun j i=> v*R.activities.E j i+s*A.activities.E j i
def traitK (R A: RG.Rep G f)(v s : ℂ) : Payload G f:= fun j i=> v*R.activities.K j i+s*A.activities.K j i
def blend (R A: RG.Rep G f)(b h s t u:ℝ) : RG.Rep G f:=ComplexVertex.replace R b (fun j i=>h*R.activities.E j i+s*A.activities.E j i) (fun j i=>t*R.activities.K j i+u*A.activities.K j i)
set_option maxHeartbeats 800000 in
lemma mix_log (A:RG.Rep G f) {e :Payload G f} {μ ν : ℂ} (he:∀ i y,e i y=μ *(R.activities.E i y)+ν*(A.activities.E i y)) (h:Facing R A) (i:ℕ):
    comboLog X R I u z O a τ e (.inl (.inl i)) = μ*logMoment X a R O u I z (.inl (.inl i)) + ν*logMoment X a A O u I z (.inl (.inl i)) := by
  have hl:=location h (n:=X.B) (l:=0) (T:=T)
  unfold logMoment frost nest Activities.regularOccurrence; simp only [Sum.elim,nest,h.params,h.reg,hl]
  rw [comboLog,h.params,h.reg,hl]
  unfold ComplexVertex.hiddenC masked; simp only [Set.indicator_apply]; split_ifs; rw [he]; push_cast; ring
  push_cast; ring
lemma mix_K (A:RG.Rep G f) {e f':Payload G f} {μ ν : ℂ} (he:∀ i y,f' i y=μ *(R.activities.K i y)+ν*A.activities.K i y) (h:Facing R A) (i l:ℕ):
    emberC X R I u z O a W k τ l e f' (.inr (.inl i))= μ*sheath X a R u I i + ν*sheath X a A u I i:= by
   simp only [emberC,Sum.elim,sheath,forcedFoot,h.forced]; rw [he]; push_cast; ring
end YM.Frontier.Tuning.Held
