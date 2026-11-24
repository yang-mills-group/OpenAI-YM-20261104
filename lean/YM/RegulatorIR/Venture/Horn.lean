import YM.RegulatorIR.Venture.Duo

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Gain plus slack and damping on χ. Does not bind projections. -/
open Epoch.League
variable {X I:Type} {M:X→ℕ}{n:Page M→Side} {K:KernelChoices}(S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→Scale){B:Marked M}
variable {p e u r:ℕ} {γ θ:ℝ} {Q : Page M→ℝ≥0∞}
section V
variable {X':Type}{M':X'→ℕ}{n':Page M'→Side} (S':Circuit M' n')(s':Page M'→Scale)(A:Section S S'){B':Marked M'}
local notation "χ"=> chi S Y G Z s
local notation "χ'"=> chi S' Y G Z s'
local notation "Ω₁"=> lnk S G
local notation "Ω₂"=> lnk S' G
local notation "A₀"=> S.devices Y G Z s
local notation "A₁"=> S'.devices Y G Z s'
local notation "β"=> B.age_t
local notation "α"=> B.age_f
section duel
-- inherit pose.B calibrations no clocks escape.
local notation "U₀"=>S.payroll Y G Z s
local notation "U₁"=> S'.payroll Y G Z s'

local notation "ψ"=> shelter S Y G Z s S' s' A
local notation "F"=> focusD S Y G Z s S' s' A
local notation "δ"=> alterB S s S' s' A -- order? S s S' s'
local notation "Ω₃"=> bumpD S Y G Z s S' s' A
-- polynomial authorization shape for both. lighter B.En.Critical.Ratio.P
variable (D:Choice M) (D':Choice M')
structure Remit (p u:ℕ)(B:Marked M)(B':Marked M')(θ γ : ℝ): Prop where
 f : Scripted S Y G Z p u B γ
 s : Scripted S' Y G Z p u B' γ
 measure i:S'.l (A.connects i)=S.l i
 width : Poly B.age_t fun i=> B'.age_t.val (A.connects i)
 θp : 0≤θ
 θv : θ<γ
 spot w:A.connects (D.choose w) = D'.choose (A.cast_r w)
 beam w:B.peak (D.choose w)=0
 wing w:B'.peak (D'.choose w)=0
variable (R: Remit S Y G Z S' A D D' p u B B' θ γ)
local notation "v"=>Reserve.maskB B θ
local notation "l"=> Reserve.peak_M B θ
include R
lemma leveled : Carry β v l:= Carry.mono (Carry.unit B.age_t v) fun i=> Reserve.meets B i R.θp
lemma expectations {Q:Flap M→ℝ≥0∞}(h:Carry α (l ∘ Flap.prev) Q): Carry α (v ∘ Flap.prev) Q:= h.charge ((leveled S Y G Z S' A D D' R).us Flap.prev)
lemma coat_v : VacDay v β (Ω₁ u) (fun i=>coil (S.scroll_j Y G i)-coil (S'.scroll_j Y G (A.connects i))):=by obtain ⟨c,h,H⟩:=cohort S Y G Z S' A R.width R.f R.s R.θv R.θp; exact ⟨_,h.charge (leveled S Y G Z S' A D D' R),H⟩
lemma lines_d : RailDay (v ∘ Flap.prev) α (drifted S G u) (fun i=> (A₀ i).line-(A₁ (A.fly i)).line):=by obtain ⟨c,h,H⟩:= rays_diff S Y G Z s S' s' A R.width R.f R.s R.θv R.θp; exact ⟨_,expectations S Y G Z S' A D D' R h,H⟩
lemma beams_d : RailDay (v ∘ Flap.prev) α (drifted S G u) (fun i=> (A₀ i).driftL-(A₁ (A.fly i)).driftL):=by obtain ⟨c,h,H⟩:= slope_diff S Y G Z s S' s' A R.width R.f R.s R.θv R.θp; exact ⟨_,expectations S Y G Z S' A D D' R h,H⟩
section transforms
-- support pins.Drift. weight rest
omit R in
private lemma hands (i:Flap M) : mainL K (S'.pactP (A.fly i)) G (Z _)=mainL K (S.pactP i) G (Z _) ∧ mainR K (S'.pactP (A.fly i)) G (Z _)=mainR K (S.pactP i) G (Z _):= by rw [A.pact];exact ⟨rfl,rfl⟩
lemma coast_k (he:e≤p)(hr:r≤p+2)(h:∀ i<e,Carry β v fun w=>‖alterB S s S' s' A i w‖ₑ) : VacDay (v∘ Flap.prev) α (drifted S G u) (fun i=> auxiliary S G Z s e r i-auxiliary S' G Z s' e r (A.fly i)):=by
 unfold auxiliary; simp_rw [fun i=>(hands S G Z S' A i).1,fun i=>(hands S G Z S' A i).2]; simp_rw [add_sub_add_left_eq_sub, ←sum_sub_distrib]; apply VacDay.sum; intro q hq
 obtain ⟨hz,hm⟩:= mem_erase.mp hq; have ht:= mem_antidiagonal.mp hm; have h₁:q.1<e:=by by_contra! hp;apply hz;exact Prod.ext (by change q.1=e;omega) (by change q.2=0;omega)
 let a:= h q.1 h₁; simp_rw [← sub_smul]; apply VacDay.rents (mainR_cost S Y G Z R.f (show q.2+2≤p+2 by omega) hr); 
 have hh: Carry α (v∘Flap.prev) fun w=> ‖alterB S s S' s' A q.1 w.prev‖ₑ:= a.us Flap.prev
 convert hh using 1; ext1 x; unfold alterB; rw [A.previous] -- Fly prev implicit
lemma lag_par (he:e ≤ p)(hr:2≤r)(h:∀ i<e,Carry β v (fun w=>‖alterB S s S' s' A i w‖ₑ))(i j:ℕ)(hp:Earlier e r i j): VacDay (v∘Flap.prev) α (drifted S G u) (fun w=>(A₀ w).addon i j-(A₁ (A.fly w)).addon i j) :=by
 have ht:i≤e:=by unfold Earlier at hp;omega
 by_cases hj:j≤p+2
 · by_cases hy:0 < i
   · simp_rw [fun w=>coast_add S Y G Z s hy j w,fun w=>coast_add S' Y G Z s' hy j w, fun i=>(hands S G Z S' A i).2,add_sub_add_comm];apply VacDay.add (coast_k S Y G Z s S' s' A D D' R (ht.trans he) hj fun j hj=>h j (hj.trans_le ht))
     cases show i<e∨ i=e ∧ r<j from hp with
     | inl H=> simp_rw [← sub_smul]; apply VacDay.rents (mainR_cost S Y G Z R.f (show 2 ≤ p+2 by omega) hj);
               have hE: Carry α (v∘Flap.prev) fun w=> ‖alterB S s S' s' A i w.prev‖ₑ:=(h i H).us Flap.prev
               convert hE using 1;ext1 x;unfold alterB;rw [A.previous]
     | inr H=> simp_rw [fun w=> paints S Y G Z w];simp_rw [peak_dark _ (show j ≠ 2 from by omega),smul_zero,sub_zero];exact zero_r
   have hp:i=0:=by omega
   subst i; simp_rw [fun w=> vacuum_lo _ (show Vacuum ((A₀ w).addon) from Halo.essential (S.lane Y G Z s) w),fun w=>vacuum_lo _ (show Vacuum ((A₁ w).addon) from Halo.essential (S'.lane Y G Z s') w), sub_self];exact zero_r
 let hp(w:Flap M): (A₀ w).addon i j=0:= Classical.not_not.mp (fun he'=>hj (le_trans ((Halo.essential (S.lane Y G Z s) w i j he').2) (by omega)))
 let hq(w:Flap M'): (A₁ w).addon i j=0:= Classical.not_not.mp (fun he'=>hj (le_trans ((Halo.essential (S'.lane Y G Z s') w i j he').2) (by omega)))
 simp_rw [hp,hq,sub_self];exact zero_r
lemma over_k (he:e≤p)(hr:2≤r)(H:∀ i<e,Carry β v fun w=>‖alterB S s S' s' A i w‖ₑ)(T:∀ i j,Earlier e r i j→ VacDay v β (Ω₁ u) fun w=>(U₀).bulk w i j-(U₁).bulk (A.connects w) i j)(i j:ℕ)(h:Earlier e r i j) :VacDay (v∘Flap.prev) α (drifted S G u) (fun w=>(A₀ w).jVac ((U₀).bulk w.prev) i j - (A₁ (A.fly w)).jVac ((U₁).bulk (A.fly w).prev) i j) :=by
 convert VacDay.add (epoch_bill S Y G Z s (T i j h)) (lag_par S Y G Z s S' s' A D D' R he hr H i j h) using 1; ext1 w; unfold GridStep.jVac; rw [offer_diff,A.previous]; exact add_sub_add_comm ..
end transforms
end duel
end V
end YM.RegulatorIR.Venture
