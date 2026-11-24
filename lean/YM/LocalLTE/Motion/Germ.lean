import YM.LocalLTE.Fan.Brink
/-! Kernel bills ready. clauses α births. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ κ k: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
local notation "K"=> Veil c f
local notation "E"=>Disk G c
variable (D:Finset (Veil c f)) (I:Finset (Tubular f G))(H: Cash W t μ L Q o a T R)(he:X.x=t)(hK:X.width=o.K)
lemma harmony {P:Teller G} (L:Side) (D:Patch)(hd:D.Branches P.bind G){p M:ℝ→ℝ}{N I:ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W)(j m n q:ℕ)(h₁:1≤j)(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hk:Reliable G κ k)(hi:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ))(hM:Rate G L 0 M):
   ∃ V:ℝ→ℝ, Rate G L 0 V ∧ ∀ᶠ t in atTop, let B:=betaF G t L
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→ ∀ (R:Rep G f) (μ σ:ℝ) (_H:Cash W t μ L Q o σ T R)(F:Forest S.ratio)(X:Coat T F), X.x=t→ X.width=o.K→∀ (Y:Finset (Tubular f G))(r:ℕ→ℕ)(φ:ℕ→ℝ), (Y.card:ℝ)≤ M t → ∀ (A:Finset (Veil c f))(w:LevelsΛ A n), (∀ i∈A, Breed R r φ B κ (N t) (I t) m i)→ A.card≤ q →
     (∀ i∈A,0≤fisc R B φ i∧fisc R B φ i≤1) → ∀ x:Disk G c, ‖x‖< p t →
     ∀ i ∈ cabinet Y (postponement L t o), Brush j (((∏ i∈A,fisc R B φ i)* B^(tones A (jumpP r) w))*|V t|) 1 (fun p=> songP X R A Q.table Y p i w) x :=by
  let d t:=postponement L t o
  have hz: Rate G L 0 d:= ((show Rate G L 0 (fun t=>Delay.fineMonitor G L t /2) from (by simpa only [div_eq_mul_inv] using! ((Rate.monitor (G:=G) (L:=L)).mul_right (2:ℝ)⁻¹))).mul_left _)
  obtain ⟨V,hv,H⟩:= Vine.newness G L D hd o.f j h₁ h hp hM hz hp'
  let v x:= V x*(1+(1+(q:ℝ)*(n:ℝ)))^j
  refine ⟨v,hv.mul_right _,?_⟩
  filter_upwards [H,Fan.stars L D hd Q W o j m h₁ hW h hp hp' hk hz hi hN,Delay.shift_pos G L] with t ht hz hB B c f S T he R μ σ H F X hX hK Y r φ hy A w ha he' h₀ x hx
  let Q₀:=fisc (c:=c) R B φ; let WC:=(∏ i∈A,Q₀ i)* B^(tones A (jumpP r) w); have hw i (hi:i∈A):0≤Q₀ i := (h₀ i hi|>.1)
  have hD : 0≤ WC:= mul_nonneg (prod_nonneg hw) (Real.rpow_nonneg hB.le _)
  have hh:= H.laws.data
  intro i hi'
  have h':0 ≤ d t:= by unfold d postponement; have hv:= Delay.monitor_pos G L t; have hx:=o.rare; positivity
  have hz' i': |Pond.spill Y i i'|≤|d t|:= (fur Y hi' h' i').trans (le_abs_self _)
  have hp:= brushL A (w:=fun p i' =>coming Q.table R X p (Pond.spill Y i) i') (fun i hi=> hz _ _ S T he R _ _ H F X hX hK r φ _ hz' x i hx (ha _ hi)) w
  have hI : Brush j (V t) 1 (fun p=> pledgeΛ X Y i (Vine.pass p)) x := by
    have he := Brush.reading sideways ((ht c f S T F X Y hX he hh.funds (hh.localP F X.blank hX hK (X.bowed (temp_nonneg _))).sails.scale hy i (fun i=> (show ∀ i₀, _ ≤ d t from fun i₀=> hi' i₀|>.trans le_rfl) i|>.trans (le_abs_self _)) (Vine.pass x) ((Vine.tally ..).trans hx.le)).1) norm_side -- edit
    rw [mul_one] at he; exact he
  apply ((hI.paints (hp.climb _ -- edit
     (mul_le_mul_of_nonneg_right (show (A.card:ℝ) ≤ q from by exact_mod_cast he') (Nat.cast_nonneg n)) : Brush j WC ((q:ℝ)*(n:ℝ)) _ _)).trim).climb _ le_rfl
  rotate_left
  · rw [show V t*WC*(1+(1+ (q:ℝ) * (n:ℝ)))^j=WC*v t by unfold v; ring]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hD
  rw [pastel A _ _ hB]; exact mul_le_mul_of_nonneg_right (paid A Q₀ hw (fun _ hi=> h₀ _ hi|>.2) w|>.2) (Real.rpow_nonneg hB.le _)
end YM.LocalLTE.Fan.Bakers
