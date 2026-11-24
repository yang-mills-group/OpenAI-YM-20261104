import YangMills.WilsonProof.NativeSupport.JointSwitch

/-! Regular connected terms and forced cluster terms from the actual measured
molecular family have the same numerical rooted majorants as the native ones. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTreeBill
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open Merge Merge.Palette Switch Mixed Daisy Blaze.March Multiple Ursell Trees OmitClusters Gas
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {F : Forest S.ratio} {R : Rep G f} {W μ x C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : ι→Leaf R) (Y : Cash W x μ L Q o C T R) (χ : Chi) (rA : ι→ℝ)
variable (marks : Tickets (Palette.sign M S)→Finset (Bond c)) (probe : Tickets (Palette.sign M S)→Bond c→ℝ→ℝ)
variable (hm : ∀ i,∀ b∈marks i,Measurable (probe i b))
variable (unit : ∀ i,∀ b∈marks i,∀ t∈Set.Icc 0 (linkCap S),‖probe i b t‖≤1)

variable (hR : Palette.Plot M Y rA)
def current (U : Config G c) (t : ℝ) (s : Finset ι) (p : Molecule S) :=
  JointSwitch.vote M Y χ rA marks probe p U t s

def regular (i : Y.fragrances) (U : Config G c) (t : ℝ) (s : Finset ι) :=
  Y.trainedMill (current M Y χ rA marks probe U t s) i

def forced (i : Y.Chainbook) (U : Config G c) (t : ℝ) (s : Finset ι) :=
  Y.smilesMill U (current M Y χ rA marks probe U t s) i

include hm unit hR
theorem regular_price (i:Y.fragrances)(k:ℕ): Paid (regular M Y χ rA marks probe i) (lace M Y rA k i):=by
  let C: ℝ:=↑((i.1+1).factorial)
  let c:= coefficient Y.seam i.2/C
  have h: lace M Y rA k i= ‖c‖ *∏ j:Option (Fin i.1), tune M Y rA 0 k ((i.2 j).val):= by
    unfold lace c C clusters; rw [Real.norm_eq_abs,abs_div, abs_of_nonneg (by positivity:0≤ (↑((i.1+1).factorial):ℝ))]; ring
  rw [h]; refine Paid.congr ((Paid.prod univ (fun j:Option (Fin i.1)=> JointSwitch.vote M Y χ rA marks probe (i.2 j).val) _ (fun j _=> JointSwitch.molecular M Y χ rA marks probe hm unit hR.live _ 0 k (Nat.zero_le _))).smul c) ?_
  intro U x hx; ext i'; unfold regular current Cash.trainedMill Gas.term; simp_rw [Pi.smul_apply,Finset.prod_apply,smul_eq_mul]; unfold c C; ring_nf; rfl
private theorem chapter_price (i:Y.Chapter)(k:ℕ): Paid (fun U t (u:Finset ι)=>Y.cologneMill (current M Y χ rA marks probe U t u) i) (grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 k i.val) (fun i:Y.ThickP=>Palette.tune M Y rA 1 0 i.val) i) := by
  rcases i with i|i
  · exact JointSwitch.molecular M Y χ rA marks probe hm unit hR.live i.val 1 0 (Cash.forced_cost i.val i.prop.2)
  exact (regular_price M Y χ rA marks probe hm unit hR i k).neg
theorem forced_price (i:Y.Chainbook)(k:ℕ): Paid (forced M Y χ rA marks probe i) (bold M Y rA k i):=by
  unfold bold; split
  next hi =>
    let c:= grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 k i.val) (fun i:Y.ThickP=>Palette.tune M Y rA 1 0 i.val)
    let f j U (t:ℝ)(u:Finset ι):=Y.cologneMill (current M Y χ rA marks probe U t u) j
    let F (j: ↥i.1) := (((↑((i.2 j + 1).factorial):ℝ)⁻¹) • (f j.val) ^ (i.2 j+1)) -- Sigma? check
    let G := ∏ j,F j
    have hp : Paid G (manyW c i):= Paid.prod univ F _ fun j _=> by
      convert! ((chapter_price M Y χ rA marks probe hm unit hR j.val k).pow (i.2 j+1)).smul _ using 1
      simp [div_eq_mul_inv,mul_comm,c]
    refine Paid.congr (Paid.gate (X:={U| Y.statesPool U i}) hp) ?_
    intro U x _; ext p
    by_cases h:Y.statesPool U i
    · rw [Set.indicator_of_mem (show U∈_ from h)]; unfold forced Cash.smilesMill; rw [if_pos ⟨hi.1,hi.2,h⟩]; unfold G manyW F; simp [f,div_eq_mul_inv,mul_comm]
    rw [Set.indicator_of_notMem (show U∉{U|Y.statesPool U i} from h)]; exact (if_neg (show ¬(_∧ _∧Y.statesPool U i) from fun he=>h he.2.2)).symm --
  next h=> refine Paid.congr paidZero (fun U x hx=>?_); ext i; exact (if_neg (show ¬(Y.Fresh _ ∧ Ac.Spark _ _ ∧ _) from fun y=> h ⟨y.1,y.2.1⟩)).symm

/-- The numerical costs on the right are exactly the campaign costs for the
unmodified mounted family. All measurements are inside the original ticket. -/
theorem hit {a e b : ℝ} {j k : ℕ} (board : Bikes Q L μ x a e b j k) (hb : 0≤b) :
    (∀ i, Paid (regular M Y χ rA marks probe i) (Palette.lace M Y rA k i)) ∧
    Ac.Hit (fun i:Y.fragrances => Y.bookFoot (.inr i)) (radiusB x) (Palette.lace M Y rA k)
      (a+e) (Daisy.pledgeA L Q μ x b j k*(1-Daisy.sailUp Q L x)⁻¹) ∧
    (∀ i, Paid (forced M Y χ rA marks probe i) (Palette.bold M Y rA k i)) ∧
    Ac.Hit Y.library (radiusB x) (Palette.bold M Y rA k) a
      (Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x b j k)) := by
  exact ⟨fun i => regular_price M Y χ rA marks probe hm unit hR i k,
    Palette.lucent M Y χ rA hR board hb,
    fun i => forced_price M Y χ rA marks probe hm unit hR i k,
    Palette.bright M Y χ rA hR board hb⟩

end YM.Integration.InletSusceptibility.JointTreeBill
