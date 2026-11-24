import YM.RG17.Plat
/-!
# Pay OPE points also just OFF this lattice. Generic tail variant; no contact. WilsonX series interpolation still needs actual purchase (at priced readouts instead of all measured points). Estimate version for physically determined packet and any forecast when associated costs/hol on axes proved separately. Predict must measure at THESE positions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Polar Extraction Word Table Metric
open Lattice RG SharpGram PhysicalNext PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{U:Spec.Final R.family f S}{L:Layout U}
variable {B:Filter (ℕ×ℕ)}{D:Lenses.Mantle U B}(Z:Ledger L)(W:Services R.family f S)(fx:Flick R.family.path.levels)(hz:Pegs D L) (P:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
set_option quotPrecheck false
local notation "T"=>OPE.run
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
variable {n:ℕ} (d: Fin n → ℕ)(t:ℕ) (v:ℝ→Labels S d) (p:GradePrice P d v 0)
    (A:Free R.family t→L[ℂ] ℂ) (u:ℝ→ℂ) (ht:RateLE home T u 0)
include p
lemma beforeFrame (i: Fin n) : RateLE home T (fun j=> v j i) 0:=by
    let k:=d i; let g(j:Fin (k+1))(r:ℝ) : S.Field k:=U.sector.derivatives.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt) (P.cutTest j.val (d i) (v r i)); have hx(r):v r i=∑ j:Fin _,g j r:=by
        have h:=P.reconstruct k k (le_refl _) (v r i); rw [U.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts] at h; exact h.symm
    apply (RateLE.sum (f:=g) ageLarge ?_).congr (Eventually.of_forall fun i=> (hx i).symm); intro j _; apply pay_fixed ageLarge ((U.sector.derivatives.rise _).restrictScalars ℝ); exact (p i _).mono (by simp)
private abbrev bid17 (r:ℝ)(x: Fin n →E4):ℂ:= u r * A (toFrame L t r (P.packet t x (v r) 0))
private abbrev roomPath {n:ℕ} (X:ℝ → Fin n → E4) (M η:ℝ):= ∀ᶠ i in home,WithinRoom i M η (X i) 0
include p hz W ht
-- finite list, flattened Sigma for one theta call. use Fin address to expose.
set_option maxHeartbeats 500000 in
lemma porch : ∃ (q:ℕ) (J:Fin q→Exterior R.family.book) (Y: Fin q → ℝ → ℂ), (∀ j,RateLE home T (Y j) (t:ℝ)) ∧ ∀ x:ℝ→Fin n→ E4, (∃ M η,0≤M ∧0<η ∧ roomPath x M η) → RateLE home T (fun i=>bid17 (L:=L) R P d t v A u i (x i) - ∑ j,Y j i * whole S (x i) (v i) (bearing (J j)) (fields S (J j))) (-1):=by
    let F':= S.Field t; let b:= Module.finBasis ℂ F'; let ξ(i:Fin _)(r:ℝ):= u r * A (toFrame L t r (b i)); have hξ (i:Fin _):RateLE home T (ξ i) t:= by
       letI:FiniteDimensional ℝ (Free C t) := Module.Finite.trans ℂ _
       apply (ht.mul (pay_fixed ageLarge ((A.restrictScalars ℝ).toLinearMap) (beacon R W t hz (RateLE.const (b i) ageLarge)))).mono; simp
    choose Y hY using fun i:Fin _=> reachReads t (b.coord i); let V(i):=((Y i).support : Type); letI (i: Fin (Module.finrank ℂ F')): Fintype (V i):=inferInstanceAs (Fintype ((Y i).support:Type)); let I:=((i:Fin _) × V i); letI:Fintype I:= Sigma.instFintype; let Q:= Fintype.equivFin I
    let k(j:(i:Fin _) × V i): Exterior R.family.book := (j.2: ((Y j.1).support : Type)).val
    let y(j:(i:Fin _) × V i)(r:ℝ): ℂ:= ξ j.1 r*(Y j.1 (k j)); have hy(j): RateLE home T (y j) (t:ℝ):=((hξ _).mul (RateLE.const _ ageLarge)).mono (le_of_eq (by simp))
    let J(j:Fin _):= k (Q.symm j); let p'(j:Fin _):= y (Q.symm j)
    have hU(j):RateLE home T (p' j) t:=hy _
    refine ⟨Fintype.card I,J,p',hU,fun x h=>?_⟩; obtain ⟨M,η,hM,hη,hk⟩:=h
    have h (z: Exterior R.family.book): ∃ δ>0,ClearOf 0 (bearing z) δ:=by
       obtain ⟨M,η,hM,hη,hv⟩:= roomCosts (K:={z.point}) (isCompact_singleton) (singleton_subset_iff.mpr z.clear)
       have he(j k)(h:j≠k):= (hv 1 one_pos z.point (mem_singleton z.point)).spaced j k h
       refine ⟨η,hη,⟨fun j=>?_,fun i j hi=>?_⟩⟩
       · simpa [posed,bearing,horizonPin,Points.head] using (he 0 j.succ (Ne.symm (Fin.succ_ne_zero _)))
       simpa [posed,bearing] using (he i.succ j.succ (Fin.succ_injective _|>.ne hi))
    let V'(i):= P.packet t (x i) (v i) 0; let w(j)(i):= S.spectra t (V' i) (J j); let Φ j i:= whole S (x i) (v i) (bearing (J j)) (fields S (J j)); have ht(j):RateLE home T (fun i=> Φ j i-w j i) (-(t+1:ℝ)):=by
        obtain ⟨δ,hδ,hL⟩:=h (J j); have h':=formulaOn P W hM hη (fields S (J j)) t p (show home≤home from le_rfl) x (fun _=>0) (fun _=>bearing (J j)) (fun _=>none) hk hδ (Eventually.of_forall fun _=>hL); simp only [Pi.zero_apply,Finset.sum_const_zero,add_zero] at h'; apply h'.congr
        filter_upwards with i; change _-_= Φ j i-w j i; congr 1; rw [← packet_read U P _ _ _ _ _ none t (bearing_clear (J j))]; exact fault17 U _ _
    apply (RateLE.sum (f:=fun j i=>p' j i * (-(Φ j i-w j i))) (S:=Finset.univ) ageLarge (fun j _=>((hU j).mul (ht j).neg).mono (by linarith only))).congr
    filter_upwards with i; simp_rw [neg_sub,mul_sub]; rw [Finset.sum_sub_distrib]; apply congr_arg (·-∑ j,p' j i*Φ j i)
    unfold p' w J; refine (Q.symm.sum_comp (fun x=> y x i * S.spectra t (V' i) (k x))).trans ?_; unfold bid17; change _= u i * A (toFrame L t i (V' i)); conv_rhs=> rw [← b.sum_repr (V' i), map_sum, map_sum,Finset.mul_sum]
    rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl; intro j _
    let f'(z:Exterior R.family.book):=Y j z*S.spectra t (V' i) z
    have hh:b.repr (V' i) j= ∑ z∈(Y j).support,f' z:=by
           change b.coord j _=_; rw [← hY,computes]
    rw [map_smul,map_smul,hh,smul_eq_mul,mul_left_comm, ← Finset.sum_attach (Y j).support f', Finset.sum_mul]
    refine Finset.sum_congr rfl ?_; intro z _; change ξ j i *(Y j z.val)* _= (Y j z.val*S.spectra t (V' i) z.val) * (ξ j i); rw [mul_assoc,mul_comm (ξ j i)]

/-- Scaled *prediction*. Against pointwise kernel version when independently constructed and meets Ports. Arguments in true units `q • r`; reference charts and g conventions must still be tied to these Lens. Rank projections post-frame. Analytic price on prediction demanded SEPARATELY for interpolation on literal clock. Sufficient. Does not assert formal perturbation functions already meet it. -/
structure Loom {n:ℕ} (A:ℝ→ (Fin n→ E4)→ℂ)(r:ℝ → Fin n→ E4) : Prop where
   demands : ∀ᶠ i in home,∀ z:Fin n→E4, ‖z‖ ≤ 1 → DifferentiableAt ℝ (fun z=>A i (centered r id i z)) z ∧ ∀ (j:Fin n)(k:Ortho), Radiates (fun z=>A i (centered r id i z)) z (ray j k) (Real.exp (run i^2))
local notation "K"=> wheel R.family
local notation "R'"=> R.family.S.gridPoint
abbrev pix {n:ℕ}(p:ℝ→Fin n→ Cover)(r:ℝ):Fin n→E4:= R' (K r) ∘ p r
include fx
lemma heard_A (p₀:Fin n) (g:ℝ→ (Fin n→E4)→ℂ) (X:ℝ→ Points n) {x:Points n}(hT:x ∈generic n)(hX:Tendsto X home (𝓝 x)) (Y:ℝ→ Fin n→ E4)(hY:Y=fun i=>posed i (X i)) (G':Loom g Y) (hg:∀ b:ℝ→ Fin n→ Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x)→∃ C₀:ℝ, ∀ᶠ i in home, ‖u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0)) - g i (pix R b i)‖≤C₀) : ∃ C₀:ℝ, ∀ᶠ i in home, ‖u i * A (toFrame L t i (P.packet t (Y i) (v i) 0)) - g i (Y i)‖ ≤ C₀:=by
    obtain ⟨q,J,c,hc,hj⟩:= porch R W hz P d t v p A u ht
    obtain ⟨a,ha,hA⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open n).mem_nhds (generic_conf n hT)); obtain ⟨M,η,hM,hη,hκ⟩:= roomCosts (isCompact_closedBall x a) hA
    have hv:roomPath Y M η:=by filter_upwards [positiveLength,hX.eventually (closedBall_mem_nhds _ ha)] with i hi hx; rw [hY]; exact hκ _ hi _ hx
    let X':= centered Y id; let F₀ i x:= ∑ j,c j i*whole S x (v i) (bearing (J j)) (fields S (J j)); let f(i)(z):= F₀ i (X' i z) -g i (X' i z);
    let κ:ℝ:=2*((Fintype.card (Fin n×Axis):ℝ)+1); have HK:1≤κ:=by unfold κ; have hx: (Fintype.card (Fin n×Axis):ℝ)≥0:= Nat.cast_nonneg _; linarith
    let T' i:= 2*T i^2; have hI:∀ᶠ i in home,2 ≤ T i:=ageLarge.eventually_ge_atTop 2; have hm:∀ᶠ i in home,1 ≤ T' i:= hI.mono fun i hi=> by unfold T'; nlinarith only [hi]
    have ha:∀ᶠ i in home,∀ z∈closedBall (0:Fin n→ E4) 1,Watches (f i) z (T' i) κ:=by
       filter_upwards [meetSum (v:=v) (R:=c) U J tendsto_id hη (x:=Y) hv,G'.demands,listRates U J tendsto_id hη v (fun j=>⟨_,beforeFrame R P d v p j⟩) c (fun j=>⟨_,hc j⟩) (x:=Y) hv,hI] with i hG hD hz ht z hu; have hc := mem_closedBall_zero_iff.mp hu; obtain ⟨hh,hq⟩:= hD z hc; have h (j:Fin n)(a:Axis) : ∃ p:Ortho, ‖(forwards p).val-basis a‖< knobSize (Fin n) ∧ Radiates (f i) z (ray j p) (Real.exp (T' i)):=by
           obtain ⟨p,hp,hT⟩:=hz z hc j a; refine ⟨p,hp,?_⟩
           have hi : Real.exp (T i^2) + Real.exp (T i^2) ≤ Real.exp (T' i):=by
               unfold T'; rw [two_mul,Real.exp_add]; let e:=T i^2; have hx :2 ≤ Real.exp (T i^2):=by nlinarith only [ht,Real.add_one_le_exp (T i^2)]
               nlinarith only [hx]
           have hy:hT=hT:=rfl; unfold f X'; simp_rw [sub_eq_add_neg]; exact hT.add (by simpa only [norm_neg,norm_one,one_mul,neg_mul] using (hq j p).smul (-1))|>.mono hi
       obtain ⟨w,-,hp⟩:=h p₀ timeAxis; exact knobs_cost (f i) _ hp.at_center ((hG z hu).sub hh) h
    have hE:∃ A,∀ᶠ i in home,‖f i 0‖≤ A:=by
       apply Joint17.hike (X:= Fin n → E4) hm (Eventually.of_forall (fun i:ℝ=>HK)) ha; intro v' hv'; obtain ⟨y,b,hQ,hρ⟩:=Joint17.hopping W.simpleGate fx HK Y v' hv'; let U i:= tag (role R.family i) (b i); have hC: Tendsto U home (𝓝 x):=by
          let RV(i):= (run i)⁻¹ • y i; have hz:Tendsto RV home (𝓝 0):=by
             refine squeeze_zero_norm' ?_ (tendsto_inv_atTop_zero.comp ageLarge); filter_upwards [ageLarge.eventually_gt_atTop 0,hρ] with i hi hx; unfold RV; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hi.le)]; exact mul_le_of_le_one_right (inv_nonneg.mpr hi.le) hx.2.1
          let Z' (v: Fin n → E4):= WithLp.toLp 2 v; have hz': Tendsto (fun i=> (Z' (RV i):Points n)) home (𝓝 0):=by
              apply ContinuousAt.tendsto (f:=fun i:Fin n→E4=>WithLp.toLp 2 i) (by fun_prop)|>.comp hz
          rw [← add_zero x]; refine (hX.add hz').congr' ?_; filter_upwards [positiveLength,hρ] with i hp hh
          apply MulAction.injective₀ hp.ne'; unfold U; dsimp only; rw [smul_add,scaledRole hp]; ext1 j; change (posed i (X i)) j+ i • (Z' (RV i):Points n) j= (R.family.S.gridPoint (wheel R.family i) ∘ b i) j; rw [← hh.2.2]; unfold centered; change (posed i (X i)) j+i • ((run i)⁻¹ • (y i j))= Y i j+(i/run i) • (y i j); rw [smul_smul,hY,div_eq_mul_inv]
       obtain ⟨A',hA⟩:=hg b hC; have hΓ: RateLE home T (fun i=>u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0))- F₀ i (pix R b i)) (-1):= by
          apply hj; refine ⟨M+η,η/2,add_nonneg hM hη.le,half_pos hη,?_⟩; filter_upwards [within_centered tendsto_id hη (X:=Y) hv,hρ] with i hi he; unfold pix; rw [← he.2.2]; exact hi (y i) he.2.1
       refine ⟨1+A',y,?_,hρ.mono fun i hi=> hi.1⟩; filter_upwards [hρ,hA,(RateIs.const ageLarge one_pos).outweigh hΓ neg_one_lt_zero ageLarge] with i hi hA hE; unfold f X'; rw [hi.2.2]; exact (norm_sub_le_norm_sub_add_norm_sub _ (u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0))) _).trans (add_le_add ((norm_sub_rev ..).le.trans hE) hA) -- name
    obtain ⟨c₁,hC⟩:=hE; refine ⟨1+c₁,?_⟩; filter_upwards [hC,(RateIs.const ageLarge one_pos).outweigh (hj Y ⟨_,_,hM,hη,hv⟩) neg_one_lt_zero ageLarge] with i hC hE; unfold f X' centered at hC; simp only [smul_zero,add_zero] at hC; exact (norm_sub_le_norm_sub_add_norm_sub _ (F₀ i (Y i)) _).trans (add_le_add hE hC)
end YM.RG17
