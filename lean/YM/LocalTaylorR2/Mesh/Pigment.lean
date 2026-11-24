import YM.LocalTaylorR2.Mesh.Haar
/-!
 # Exact bills for full Haar expansion; unrestricted geometry.
 Include the existing displayed Profile cut at EACH use of an actual individual argument.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port Channel Next.Foundations Itinerary Glass Zest
open Work.G05
variable {Ñ:ChartRatio G} {i p:ℕ} {b:Bond f} {v d A:ℝ}
def part (H:Cash W s μ L Q o C T R) (p:ℕ) (q:LogIndex c f):Port.Test T:=
  match q with
  | .inr (.inl (.inr (.inr i)))=> quanta H p i
  | _ => weightLog H q
def error (g : LogIndex c f→ Port.Test T) (H : Cash W s μ L Q o C T R) (q:LogIndex c f) : Port.Test T:= fun F X w=>weightLog H q F X w - g q F X w
lemma control (H:Cash W s μ L Q o C T R) (i:LogIndex c f): Kept H (H.supportP (identityLog i)) (part H p i):=by
  rcases i with i|(i|i|i)|i <;> first | exact logTest H _ | exact sealH ..

lemma payHa (Ñ:ChartRatio G) (hÑ:LocalRatio Ñ) (D:ℝ→ℝ) (V : Rate G L (-(1/2)) D) (A:ℝ) (p i:ℕ) (χ:Chi):
    ∃ X : ℝ→ℝ, Rate G L (-(p+1)/2) X ∧ ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio) (Y:Coat T F), Y.χ=χ → Y.x=x → S.patch.L=L → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z:Air f G) (a:ℝ) (y:E) (O : E→ Config G c) (f':E→ Directions G f) (f:E→Air _ G), Clutch Y Z A a (D x) y i O f' f → ∀ j, Brush i (|X x|) 1 (fun t=>Y.solo (f' t) Ñ A j - profile Ñ p Y A (f' t) j) y :=by
  obtain ⟨B,hB,hP⟩:= Clutch.kernels G L χ V i (2*A)
  let J: G.Color→ ℝ:= fun x=>Real.log (Ñ.J x)
  have hJ : ContDiffAt ℝ ω J 0:= (hÑ.germ 0 (Metric.mem_ball_self hÑ.patch)).log (by rw [hÑ.anchored]; norm_num)
  obtain ⟨M,hM,hp⟩:=Brush.neighborhood (k:=i+p+1) 0 (hJ.of_le le_top)
  obtain ⟨u,hu,hy⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp hp
  have hh {p : ℝ→ℝ}{t:ℝ}(h:Rate G L t p):Rate G L t (fun x=>|p x|):= h.compare (Eventually.of_forall fun i=>(abs_abs _).le)
  let t x := |D x|+2*(2*A)*Pressure.fiery G x L; have ht:Rate G L (-(1/2)) t:= (hh V).add (Rate.flame.mul_left (2*(2*A)))
  let v x:=1+(|B x|+1); have hv: Rate G L 0 (fun x=> v x^i):=by simpa only [zero_mul] using! (((Rate.const 1).add ((hh hB).add (Rate.const 1))).pow i)
  let K := (i.factorial * M)*(1+((1+1)*1))^i
  refine ⟨fun x=>(K*t x^(p+1))*v x^i,?_,?_⟩
  · convert (((ht.pow (p+1)).mul_left K).mul hv) using 1; push_cast; ring
  filter_upwards [ht.below (by norm_num) (min u 1) (lt_min hu zero_lt_one),hP] with x ht hP c f S T F Y hY hx hz E _ _ z a y O f' e H i'
  have hB:0< 2*A*Y.t:= by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  obtain ⟨ht,hV⟩:=le_min_iff.mp ((le_abs_self _).trans ht)
  have hy' : 0 < t x:=by rw [show Y.t = Pressure.fiery G x L from by unfold Coat.t; rw [hx,hz]] at hB; unfold t; linarith [abs_nonneg (D x)]
  by_cases hL : i'∉ Y.plaza (Y.seeds.dome (304*Y.B)) ∧ Y.Hot i'
  · have hf : (fun x=> Y.solo (f' x) Ñ A i'- profile Ñ p Y A (f' x) i')=fun x=> Y.cone (2*A) (f' x) i'* ((J-blockTaylor p J) (f' x i')):= by ext; simp only [solo,profile,if_pos hL,Coat.gentry, Pi.sub_apply,curved]; dsimp [J]; ring
    rw [hf]
    by_cases hj:(fun u=> Y.cone (2*A) (f' u) i')=ᶠ[𝓝 y] fun _=>0
    · exact Brush.zi (hj.mono (fun y h=> by change Y.cone _ _ _*_=_; rw [show Y.cone _ _ _=0 from h,zero_mul])) (abs_nonneg _) zero_le_one
    have he:Brush i (t x) 1 (fun t=> f' t i') y:=by have h:=(H.fostered i' hB hj).2; unfold Coat.t at h; rw [hx,hz] at h; exact h.climb (add_le_add_left (le_abs_self _) _) le_rfl
    have hk' := priced hy' hV (fun x hb=> hy (mem_closedBall_zero_iff.mpr (hb.trans ht))) he
    exact (((hP c f S T F Y hx hz hY hB E z _ _ y O f' _ H i').paints hk').trim).climb (by rw [one_mul]; exact le_abs_self _) le_rfl
  simp_rw [profile,solo, if_neg hL,sub_zero]; exact (certified zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl

lemma errorLaw (Ñ:ChartRatio G) (hÑ:LocalRatio Ñ)(a:ℝ) (D:ℝ→ℝ)(V:Rate G L (-(1/2)) D)(p i:ℕ)(χ:Chi):
    ∃ U, Rate G L (-(p+1)/2) U ∧ (∀ x,0≤U x) ∧ ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(W μ C:ℝ) (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(o:Target.Order G W)(R:Rep G f)(H:Cash W x μ L Q o C T R), Ñ=Q.table → a=o.a → ∀ v j, Sees H i v (D x) χ (error (part H p) H (.inr (.inl j))) (U x) 1:=by
  obtain ⟨U,hU,h⟩:=payHa Ñ hÑ D V a p i χ
  refine ⟨fun x=> |U x|, hU.compare (Eventually.of_forall fun _=> (abs_abs _).le),fun x=> abs_nonneg _,h.mono ?_⟩
  intro x hp c f S T W μ C P Q o R H hN ha v j E _ _ _ F X V u z y Z hX hw hm hχ _ hU; subst Ñ a
  rcases j with j|j|j
  · simp_rw [error,part,sub_self]; exact (certified zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  · simp_rw [error,part,sub_self]; exact (certified zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  change Brush i (|U x|) 1 (fun y=> X.solo (worldZ (vary X (V y)) _ _) _ _ _-profile _ p X o.a (worldZ (vary X (V y)) _ _) _) y; simp_rw [hU.moving]
  exact hp c f S T F X hχ hX H.laws.data.funds.length_eq E Z _ _ _ _ _ hU _
end YM.LocalTaylorR2.Mesh
