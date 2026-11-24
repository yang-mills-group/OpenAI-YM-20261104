import YM.RGComparison01.Marks.Hard
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Resin
open Multiple OmitClusters Palette Switch Daisy
variable [Fintype ι]
variable (M:ι→Leaf R) (ρ:ι→ℝ) (H:Cash W s μ L Q o C T R)
local notation "q" => Q.mark L μ s
local notation "Pp" => H.faresP
local notation "Xg" => Palette.sign M S
set_option quotPrecheck false
local notation "p₀"=> fun i:H.ThinP=> tune M H ρ 0 0 i.val
local notation "p₁"=> fun i:H.ThickP=> tune M H ρ 1 0 i.val

variable (χ : Chi)
variable (hi:∀ i,0≤ρ i)
include hi
lemma aur (i:H.fragrances)(k:ℕ): Paid (song M H χ ρ i) (lace M H ρ k i):=by
  let C: ℝ:=↑((i.1+1).factorial)
  let c:= coefficient H.seam i.2/C
  have h: lace M H ρ k i= ‖c‖ *∏ j:Option (Fin i.1), tune M H ρ 0 k ((i.2 j).val):= by
    unfold lace c C clusters; rw [Real.norm_eq_abs,abs_div, abs_of_nonneg (by positivity:0≤ (↑((i.1+1).factorial):ℝ))]; ring
  rw [h]; refine Paid.congr ((Paid.prod univ (fun j:Option (Fin i.1)=> vote M H χ ρ (i.2 j).val) _ (fun j _=> votes M H χ ρ hi _ 0 k (Nat.zero_le _))).smul c) ?_
  intro U x hx; ext i'; unfold song Cash.trainedMill Gas.term; simp_rw [Pi.smul_apply,Finset.prod_apply,smul_eq_mul]; unfold c C; ring_nf; rfl
lemma chap (i:H.Chapter)(k:ℕ): Paid (fun U t (u:Finset ι)=>H.cologneMill (color M H χ U (ways ρ t u)) i) (grade H.seam (fun i:H.ThinP=> Palette.tune M H ρ 0 k i.val) p₁ i) := by
  rcases i with i|i
  · exact votes M H χ ρ hi _ 1 0 (Cash.forced_cost i.val i.prop.2)
  exact (aur M ρ H χ hi i k).neg
lemma aurs (i:H.Chainbook)(k:ℕ): Paid (fete M H χ ρ i) (bold M H ρ k i):=by
  unfold bold; split
  next hiY =>
    let c:= grade H.seam (fun i:H.ThinP=> Palette.tune M H ρ 0 k i.val) p₁
    let f j U (t:ℝ)(u:Finset ι):=H.cologneMill (color M H χ U (ways ρ t u)) j
    let F (j: ↥i.1) := (((↑((i.2 j + 1).factorial):ℝ)⁻¹) • (f j.val) ^ (i.2 j+1)) -- Sigma? check
    let G := ∏ j,F j
    have hp : Paid G (manyW c i):= Paid.prod univ F _ fun j _=> by
      convert! ((chap M ρ H χ hi j.val k).pow (i.2 j+1)).smul _ using 1
      simp [div_eq_mul_inv,mul_comm,c]
    refine Paid.congr (Paid.gate (X:={U| H.statesPool U i}) hp) ?_
    intro U x _; ext p
    by_cases h:H.statesPool U i
    · rw [Set.indicator_of_mem (show U∈_ from h)]; unfold fete Cash.smilesMill; rw [if_pos ⟨hiY.1,hiY.2,h⟩]; unfold G manyW F; simp [f,div_eq_mul_inv,mul_comm]
    rw [Set.indicator_of_notMem (show U∉{U|H.statesPool U i} from h)]; exact (if_neg (show ¬(_∧ _∧H.statesPool U i) from fun he=>h he.2.2)).symm --
  next h=> refine Paid.congr paidZero (fun U x hx=>?_); ext i; exact (if_neg (show ¬(H.Fresh _ ∧ Ac.Spark _ _ ∧ _) from fun y=> h ⟨y.1,y.2.1⟩)).symm
structure Ringlet (M:ι→Leaf R)(ρ:ι→ℝ)(a δ A B:ℝ): Prop where
  pays : ∀ i,0≤ ρ i
  value : 0 ≤ a
  dust : 0 < δ
  slow : Ready H.smallAt (radiusB s) (fun i:H.ThinP=> Palette.tune M H ρ 0 0 i.val) (a+δ) A δ (1/2)
  fix : Ac.Hit H.largeAt (radiusB s) (fun i:H.ThickP=> Palette.tune M H ρ 1 0 i.val) (a+δ) (Real.exp (-Q.mark L μ s)*A)
  charges : 16*A≤B
  pass : 0<B
  books : B≤1/2
  degrees : degreePrice (radiusB s) B δ ≤1/2
omit hi
variable (he:Ringlet H M ρ a δ A B)
include he
local notation "L'" => lace M H ρ 0
local notation "b0" => bold M H ρ 0
lemma breva : Ac.Hit (fun i:H.fragrances=>H.bookFoot (.inr i)) (radiusB s) L' (a+δ) (A*(1-1/2)⁻¹):=by
  intro i; have hz := log_hit_tail H.seam H.smallAt (radiusB s) H.testS he.slow (add_nonneg he.value he.dust.le) 0 i
  simp only [Nat.zero_le,pow_zero,mul_one,true_and] at hz; convert! hz using 2
lemma ern : Ac.Hit H.library (radiusB s) b0 a (Real.exp (-q)*(2*B)):=by
  intro i; have hA:= H.laws.acquired.marked; have hv : (2*Real.exp (q)*(1-1/2:ℝ)⁻¹)*(Real.exp (-q)*A) +2*(1-1/2:ℝ)⁻¹*(A*(1-1/2)⁻¹) ≤B:= by
    have hz:=he.slow.1
    calc _ = 12*A:= by rw [Real.exp_neg]; field_simp; ring
         _ ≤ B:= by linarith only [he.charges,hz]
  have ht:= OmitClusters.restore H.seam H.smallAt H.largeAt p₀ p₁ (radiusB s) he.slow.2.2.2.2.1 (fun i=> (votes M H (χ:=Chi.canonical) ρ he.pays _ 1 0 (Cash.forced_cost i.val i.prop.2)).rocket)
    (fun i=>i.2.1) (fun i=>i.2.1) (by norm_num: (1:ℝ)≤2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1) hA he.value he.dust H.testS he.slow he.fix hv he.pass he.books he.degrees (by norm_num : (1:ℝ)/2<1) i 0
  have hu:=show ( ((2:ℝ)^ (0:ℕ))⁻¹ * Real.exp (-q))*(B*(1-1/2)⁻¹)= Real.exp (-q)*(2*B) from by ring
  dsimp only at ht; rw [show (Q.costs L μ R.beta s C).markSeed=(q) from rfl,hu] at ht; refine budget_mono ht (fun i' => ?_) fun m=>?_
  · split; exact mul_nonneg (Paid.rocket (aurs M ρ H Chi.canonical he.pays _ _)) (Real.exp_pos _).le; exact le_rfl
  split
  next h=>
    unfold bold; split
    next hz => rw [if_pos ⟨H.regains m hz.2 hz.1,Nat.zero_le _⟩,Multiple.connected, if_pos ⟨hz.2,h⟩]; exact (mul_comm ..).le
    rw [zero_mul]; exact ht.1 _
  next=> exact ht.1 _
end Resin
end YM.RGComparison01.Pledge
