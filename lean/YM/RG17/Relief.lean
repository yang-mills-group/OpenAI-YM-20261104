import YM.RG17.EarlyFare
import YM.RG17.Cutter
/-!
# L1 variation payment through ALL configurations and masks, over actual Haar, after sector readout.

Does not trim denominator at base V or silently reconstruct from a different
history. Stow.earnedHere used bounded tilt; here in service of iteration spend
DIRECT ratio on any integrable tilted bill, may choose base varying per V', tag
and scale. Does not require uniform volume bounds on numerator. Keeps all
sectors before price. A D0 consumer estimate on alternative REAL output, NOT
an upstream slope or variation credit. NO smoothness or derivative promises for
edited approximants. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Lattice RG Pressure Shoot Supply Wilson MeasureTheory Finset
open PhysicalNext.Repeat.Legato RG01 RG01.Kernel
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{p N m:ℕ} (h:C.Makes)(hm:m<N)
local notation "μ"=> prior G
local notation "I" => C.path
local notation "S"=>C.path.levels.clock.op m p
local notation "β"=>C.path.β N p (m+1)

-- wrap normalized insertion outputs
def jacket (C:Family G)(N p m:ℕ)(F:Config G (C.side m p)→ℂ)(V:Config G (C.side m p)):ℂ:= boardMass C N p m V * F V

def pants {C:Family G}(N p m:ℕ)(F:Config G (C.side m p)→ℂ)(V:Config G (C.side m p)):ℂ:= F V / boardMass C N p m V

include h
omit hm in
lemma outfits (hv:m≤ N)(F:Config G (C.side m p)→ℂ): jacket C N p m (pants N p m F)=F:=by
    funext i; unfold jacket pants; field_simp [show (boardMass C N p m i:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (boardPos h N p hv i).ne']
include hm

set_option maxHeartbeats 300000 in
lemma keepsBudget (F:Config G (C.side (m+1) p)→ℂ)(hf:Integrable (jacket C N p (m+1) F) (μ _)) :
    jacket C N p m (fun V=> Kernel.conditional C.path N m p V (fun _=>F)) = share C N p m (jacket C N p (m+1) F):=by
  funext V
  let s:=S; let D:=Config G (C.side (m+1) p); let R:=upper I N p m; let b:= R.beta; let x:=boardMass C N p m V
  let L:= jacket C N p (m+1) F
  let e:= Kernel.expense I N m p V
  let H:= C.path.levels.transition_mass m p β
  let Z(i:s.Choices)(U:D):= s.likelihood U i*s.noise R.beta (s.prediction U i) V
  have hV : (x:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (boardPos h N p hm.le V).ne'
  have hh:= ((I).levels.blocks m p).branches
  have hp(i:s.Choices)(U:D) :0 ≤ Z i U:=mul_nonneg (s.likelihood_pos ..) (prod_nonneg fun j _ => mul_nonneg (inv_nonneg.mpr (s.penaltyZ_pos _).le) (Real.exp_pos _).le)
  have hp'(i:s.Choices)(U:D): Z i U≤ s.density β U V:=single_le_sum (f:=fun i=> Z i U) (fun i _=> hp i U) (Finset.mem_univ _)
  have ht(i:s.Choices): Measurable (Z i):=by
    let Q(W:D): Config G (C.side m p)×Config G (C.side m p):=(s.prediction W i,V)
    have he: Measurable Q:=(s.prediction_meas hh i).prodMk measurable_const
    have hE:= Measurable.comp (s.noise_cont (G:=G) R.beta |>.measurable) he; exact (s.likelihood_meas hh i).mul hE
  have hg(i:s.Choices): Integrable (fun U=>Z i U • L U) (prior G (C.side (m+1) p)):=by
    obtain ⟨M,hM⟩:= (show s.IsKernel β G from H).bound
    exact hf.bdd_smul M (ht i).aestronglyMeasurable (ae_of_all _ (fun U=>(Real.norm_of_nonneg (hp i U)).trans_le ((hp' i U).trans (hM U V))))
  have hq(U:D): s.density β U V • L U= ∑ i:s.Choices, Z i U • L U := Finset.sum_smul
  change (x:ℂ)*(∑ i:s.Choices,(∫ U:D,(e i U:ℂ)*F U∂prior G (C.side (m+1) p)))= ∫ U:D,s.density β U V • L U ∂prior G (C.side (m+1) p)
  simp_rw [hq]
  rw [Finset.mul_sum, MeasureTheory.integral_finsetSum _ (fun i _=> hg i)]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with u
  have he:e i u=Z i u * R.eval u / x:=rfl
  rw [Complex.real_smul,he]; change (x:ℂ)* (_*F u)= _* ((↑(R.eval u):ℂ) * F u); push_cast; field_simp [hV]

omit h hm in
lemma condTakes (g: Config G (C.side (m+1) p)→ℂ)(hg:Integrable g (μ _)) :
    (∫ V, ‖share C N p m g V‖ ∂μ _) ≤ ∫ V,‖g V‖ ∂μ _:=by
   let b(V):=(S).push β (fun W=> ‖g W‖) V; let P:=C.path.levels.transition_mass m p β
   have ht: (∫ V,b V ∂μ _) = ∫ V,‖g V‖ ∂μ _:=StepData.push_integral P _ hg.norm
   rw [← ht]
   apply MeasureTheory.integral_mono ((StepData.push_integrable P _ hg).norm) (StepData.push_integrable P _ hg.norm) fun V=>?_
   unfold StepData.push
   apply (norm_integral_le_integral_norm ..).trans (le_of_eq ?_); apply integral_congr_ae; filter_upwards with W
   rw [norm_smul_of_nonneg (show 0≤ _ from (show (S).IsKernel β G from P).positive ..),smul_eq_mul]

section relief
variable {R:Run G}{H:BeaconP R N p m}{O:woodsP R m p} {d:ℕ} {c k:ℝ}(hx:discards R H O d c) (hk:0≤ k)
local notation "U" => R.family
local notation "I'" => Config G (R.family.side m p)
local notation "J" => Config G (R.family.side (m+1) p)

structure homeEdits (R:Run G)(p m:ℕ) where
   shake : Config G (R.family.side m p) → Config G (R.family.side m p)
   area : Config G (R.family.side m p)→Support (R.family.side m p)
   meas : Measurable shake
   fit (V) : Agrees ((area V):Set (Site ..))ᶜ (shake V) V
   tap : Config G (R.family.side m p)→ Edge (Site (R.family.side m p)) → ℝ
   heels (V i) : tap V i=0→ V i=shake V i

variable (E:homeEdits R p m)

def alter (H:BeaconP R N p m)(O:woodsP R m p)(d:ℕ)(g:J→ℂ)(V:I'):ℂ:= collectible R H O d (E.shake V) (E.tap V) (fun _=>g) V
def tills (H:BeaconP R N p m)(d:ℕ) (V:I'):ℝ:= chips R H d V / chips R H d (E.shake V)
include hx hm
omit h
lemma jacketed (g:J→ℂ)(hf:Integrable (jacket U N p (m+1) g) (μ _)) :
   jacket U N p m (alter E H O d g)= tills E H d • share U N p m (jacket U N p (m+1) g) :=by
   rw [← keepsBudget (C:=U) R.makes hm g hf]; funext V
   simp only [jacket,alter,parted hx hm (E.shake V) V (E.tap V) (E.heels V)]
   change _= tills E H d V • (_:ℂ); rw [Complex.real_smul]; unfold tills jacket; ring

omit hm in
private lemma tillage : Measurable (tills E H d):=by
    have hv:=hx.2.1.smooth
    have ht: Measurable (chips R H d):= ((Measurable.tsum (fun i=>masked_measurable _ _ _ (hv i).borel)).neg).exp
    exact ht.div (ht.comp E.meas)

variable (hV:∀ V,Real.exp (pieces17 R N m p d (halo 8 (E.area V)).card c)-1 ≤ k)
include hV hk
omit hk hm in
lemma tall (V:I') : ‖(1:ℝ) - tills E H d V‖ ≤ k:= (quivers hx (E.area V) (E.shake V) V (E.fit V)).trans (hV V)
omit hk hm in
lemma tall_all (V:I') : ‖tills E H d V‖ ≤ 1+k:=by
    apply le_trans (b:= ‖(1:ℝ)‖ + ‖(1:ℝ)-tills E H d V‖) (by simpa using norm_sub_le (1:ℝ) (1- tills E H d V)); rw [norm_one]; exact add_le_add_right (tall hx E hV V) _

omit hk in
lemma earnt (g:J→ℂ)(hf: Integrable (jacket U N p (m+1) g) (μ _)) : Integrable (jacket U N p m (alter E H O d g)) (μ _) :=by
   rw [jacketed hm hx E _ hf] -- order?
   exact (StepData.push_integrable ((U).path.levels.transition_mass ..) _ hf).bdd_smul (1+k) (tillage hx E).aestronglyMeasurable (ae_of_all _ (tall_all hx E hV))

-- output bills with level norm written out to avoid ambiguity
set_option maxHeartbeats 300000 in
lemma lossTill {B:Book U p}(hB:Shelved U N p B)(g:J→ℂ) (hf:Integrable (jacket U N p (m+1) g) (μ _)) :
   (∫ V, ‖B m V - jacket U N p m (alter E H O d g) V‖∂μ _) ≤ k * Shelved.price m B + (1+k)*(∫ W,‖B (m+1) W - jacket U N p (m+1) g W‖∂μ _):=by
    let f:= jacket U N p (m+1) g; let x:=B (m+1)-f; let y:= share U N p m f; let V':=share U N p m x
    have hu: Integrable f (μ _):=hf
    have hh:Integrable x (μ _):= (hB.intake hm).sub hu
    have ha:Integrable V' (μ _):= StepData.push_integrable ((U).path.levels.transition_mass ..) _ hh
    have ht:B m=V'+y:=by
      have he:x+f=B (m+1):= sub_add_cancel _ _
      rw [hB.carry m hm, ← he]; exact StepData.push_add ((U).path.levels.transition_mass ..) _ _ hh hu
    have hv(V:I') : ‖B m V - jacket U N p m (alter E H O d g) V‖ ≤ k * ‖B m V‖ + (1+k)*‖V' V‖:=by
       rw [jacketed hm hx E _ hf]
       let s:= tills E H d V
       change ‖B m V - s • y V‖ ≤ _
       have he:B m V=V' V+y V:=congr_fun ht V
       rw [show B m V-s • y V=(1-s) • B m V+s • V' V by rw [sub_smul, one_smul, he, smul_add]; abel]
       apply (norm_add_le ..).trans; rw [norm_smul, norm_smul]; exact add_le_add (mul_le_mul_of_nonneg_right (tall hx E hV _) (norm_nonneg _)) (mul_le_mul_of_nonneg_right (tall_all hx E hV _) (norm_nonneg _))
    have hi:Integrable (B m) (μ _):= hB.intake hm.le
    have he':(∫ W, ‖B m W - jacket U N p m (alter E H O d g) W‖∂μ _) ≤ ∫ W, k*‖B m W‖+(1+k)*‖V' W‖∂μ _:= MeasureTheory.integral_mono ((hi.sub (earnt hm hx E hV g hf)).norm) ((hi.norm.const_mul k).add (ha.norm.const_mul (1+k))) hv
    apply he'.trans; rw [integral_add (hi.norm.const_mul k) (ha.norm.const_mul (1+k)),integral_const_mul k,integral_const_mul (1+k)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (condTakes (N:=N) x hh) (by linarith only [hk])) _ -- args inspect
end relief
end YM.RG17
