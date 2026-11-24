import YM.OPE.Compatible.Grout.Span
import YM.Further.DENSE_MIXED_KERNELS.Compliance
/-!
 # Compare normalized posterior to a held-ball by one physical graining. All sign matters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X:Support f}{b k: Config G f→ℝ}
def mellow (R:Rep G f)(X:Support f)(U:Config G f):=R.eval U-smudge R X U
variable (hR:R.Lawful σ C Λ E w)
include hR
lemma stamps (X:Support f): Envelope (mellow R X) ∧ GaugeInvariant (mellow R X):=by
   constructor; · unfold mellow;simpa only [mellow,sub_eq_add_neg] using (Envelope.add (R.envelope hR) (smudge_env hR X|>.neg))
   intro k U; unfold mellow smudge; have h:=Further.DenseMixedKernels.Throng.phase hR k U
   have hs:= hR.labels.forced; unfold Rep.eval Activities.gas; simp only [h,stained]; apply congr_arg₂ (·-·)
   · unfold Activities.gasOccurrence; apply congr_arg; refine tsum_congr fun b=>?_ ; simp only [Activities.admissible,RG.gauge_flags,hs.sym _ k U];split_ifs<;>rfl
   apply tsum_congr; intro i; unfold Activities.gasOccurrence; simp only [Activities.admissible,RG.gauge_flags,hs.sym _ k U];split_ifs<;>rfl
omit hR in
lemma Sable.ped (h:Sable R S X W b C):Pedal S b:=by
    intro k hk U; obtain ⟨I,hi,Z,m,w,h,hp,hL⟩:=h; rw [← (hL U).tsum_eq, ← (hL (gauge k U)).tsum_eq]; apply tsum_congr; intro i; obtain ⟨x,hH,h,he⟩:=h i; exact h.pedal k hk U
section fixture
variable {V:Config G c}(hS:S.IsKernel R.beta G)(he:∀ U,0≤R.eval U)
include hS he
lemma cuban (hx:Envelope b) {P:ℝ} (hP:∀ U,‖b U‖≤P): ‖S.push R.beta (R.eval*b) V‖ ≤ S.push R.beta R.eval V*P:=by
   unfold StepData.push; rw [← integral_mul_const]; apply (norm_integral_le_integral_norm _).trans
   apply integral_mono ((StepData.push_slice hS V (R.eval*b) ((R.envelope hR|>.mul hx).integrable _)).norm) ((StepData.push_slice hS V R.eval ((R.envelope hR).integrable _)).mul_const _)
   intro U; dsimp only;rw [norm_smul,Pi.mul_apply,norm_mul,Real.norm_of_nonneg (hS.positive U V),Real.norm_of_nonneg (he U),smul_eq_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hP _) (he _)) (hS.positive U V)
local notation "Z"=> S.push R.beta R.eval V
variable (hp:0≤a)(hP:Besotted R S a r V w) (hv:0≤ r) (hx:0≤ S.push R.beta R.eval V)
include hp hP hv hx
lemma paint (hh:X.Nonempty)(hw:0≤w){t z:ℝ}(ht:0<t)(hg:4*Shade R*w ≤ t) (hc:Sable R S X (a+t) k z)(hZ:z≤1)(hk:Paced R X S b x) (hH: S.push R.beta (fun U=> mellow R X U*(b U*Real.exp (k U))) V=0):
    ‖S.push R.beta (fun U=> R.eval U*b U) V‖ ≤ Z*x*( 2*z+ Real.exp ((a+t)*coverNumber R.p.B X)*(4*Shade R*w/t)*r*Real.exp z):=by
     let e:Config G f→ℝ:=fun U=> Real.exp (k U); have hs := (Sable.solitary (r:=a+t) hk).multiplication (hc.expo (add_nonneg hp ht.le)) (add_nonneg hp ht.le); have hP' := vast hR hP hp hv hx hw ht hg hh hS hs
     have hz:= hc.present (add_nonneg hp ht.le); let P :Config G f→ ℝ:=R.eval; let z' := smudge R X; have hf : Envelope (b*e):=(hs.present (add_nonneg hp ht.le)).1
     have hb : Envelope (R.eval * (b-b*e)):= R.envelope hR|>.mul (by simp_rw [sub_eq_add_neg]; exact hk.env.add hf.neg)
     have hu : (fun U=>P U*b U)=mellow R X * (b*e) + z'*(b*e)+R.eval*(b-b*e):=by
       funext i; change P i*b i=(P i-z' i)*(b*e) i+z' i*(b*e) i+P i*(b i-(b*e) i); ring
     rw [show (fun U=>R.eval U*b U)= _ from hu]; have hG:= (stamps hR X).1.mul hf; have ht' := (smudge_env hR X).mul hf; rw [StepData.push_add hS (mellow R X * (b*e) + z'*(b*e)) (R.eval*(b-b*e)) ((hG.add ht').integrable _) (hb.integrable _),StepData.push_add hS (mellow R X*(b*e)) (z'*(b*e)) (hG.integrable _) (ht'.integrable _), Pi.add_apply,Pi.add_apply, show S.push R.beta (mellow R X * (b*e)) V=0 from hH, zero_add]
     apply (norm_add_le ..).trans; refine (add_le_add hP' (cuban hR hS he (b:=b-b*e) (P:=x*(2*z)) ?_ ?_)).trans_eq ?_
     · simp_rw [sub_eq_add_neg]; exact hk.env.add hf.neg
     · intro i; have hx:=hz.2 i; have he': |k i|≤1:=hx.trans hZ
       change ‖b i-b i* Real.exp (k i)‖ ≤ _; rw [Real.norm_eq_abs,abs_sub_comm, show b i* _-b i=b i*(Real.exp (k i)-1) by ring, abs_mul]; exact mul_le_mul (hk.bound _) ((Real.abs_exp_sub_one_le he').trans (by change |_| ≤ _ at hx; linarith)) (abs_nonneg _) hk.safe
     ring
end fixture
end YM.PhysicalNext.Repeat.Aroma
