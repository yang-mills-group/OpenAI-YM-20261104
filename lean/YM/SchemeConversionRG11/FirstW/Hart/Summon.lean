import YM.SchemeConversionRG11.FirstW.Hart.Sheath
/-! Actual spanning on H_m test spaces via the lintelled kernel at the top of curl. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell Next.Rank.CellsInt
open Extra.FD
open scoped BigOperators Classical ContDiff
open Push.FiniteDetection.Free.Hyper hiding flip pull
variable {G : Gauge} {j k : ℕ}
def livej (A : Field4 G) (hA : A∈cabin G k) (H : ∀ i k,curlK A i k∈ Loft _ j) : Sol G.Color j := ⟨_,dome A hA H⟩
lemma signal_r (s : Signed) (A : Field4 G) (hA : A∈cabin G k) (H : ∀ i k,curlK A i k∈ Loft _ j) :
     Bare.wideCore G j 0 (Bare.wideLink G s A) = Bare.components (gaugeJet (turn s (livej A hA H))) := by
  funext i a p; rw [Bare.wideCore_apply]; change (↑j.factorial:ℝ)⁻¹ • ∑ q:Finset (Fin j), _ • curlK (Bare.wideLink G s A) i a _ = _
  rw [show (∑ q:Finset (Fin j), Bare.sign q • curlK (Bare.wideLink G s A) i a (0+∑ i∈q,step (p i)))=_ from (jumps_supply _ p _ 0).symm]
  rw [slide_curl,jumps_scale,Pi.smul_apply, jumped _ _ _ (H _ _)]
  unfold Bare.components; rw [match_leg]; change _=turns s (leaf j (curlK A)) i a _; rw [apply_turns, show Rₛ s ∘ (fun u=>basis (p u)) = (fun u=>violet s (p u) • basis (s.perm (p u))) from funext (fun u=>moves_basis ..), (leaf j (curlK A) (s.perm i) (s.perm a)).map_smul_univ]
  rw [show leaf j (curlK A) (s.perm i) (s.perm a) (fun u=> basis (s.perm (p u))) = _ from fertile (fun t : Fin j→ Axis=>(j.factorial:ℝ)⁻¹ • jumps j t (curlK A (s.perm i) (s.perm a)) 0) (s.perm ∘ p)]
  simp only [sign₂,smul_smul]; change _=(violet s i *violet s a*_ : ℝ) • _; congr 1;ring
lemma drafted_sig (A : Field4 G) (hA : A∈cabin G k) (H : ∀ i k,curlK A i k∈Loft _ j) : Bare.wideLinear G j 1 (0:Cover) A = gaugeJet (livej A hA H) := by
  unfold Bare.wideLinear; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,one_zpow, one_smul,affine, Signed.act_zero,add_zero]
  simp_rw [signal_r _ A hA H];
  have he (s : Signed) : Labels.Taylor.turn s.ortho (Bare.radialMap (Bare.components (gaugeJet (turn s (livej A hA H))))) = gaugeJet (livej A hA H) := by rw [show Bare.radialMap _= _ from Bare.complete (gaugeJet (turn s (livej A hA H))), gaugeTurn, ← Labels.Taylor.turn_mul, mul_inv_cancel ]; simp -- turn_mul direction/sign
  simp_rw [he,Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul, inv_mul_cancel₀ (show (↑(Fintype.card Signed):ℝ)≠0 by exact_mod_cast Fintype.card_ne_zero)]; exact one_smul ..
def signal (j : ℕ) : Field4 G→ₗ[ℝ] Sol G.Color j := Extra.FD.sendTo G j ∘ₗ Bare.wideLinear G j 1 0
lemma sound (A : Field4 G) (hA:A∈cabin G k) (H : ∀ i k,curlK A i k∈Loft _ j) : signal j A=livej A hA H := by rw [signal,LinearMap.comp_apply,drafted_sig _ hA H,Extra.FD.sends_back]
lemma silent (A : Nu G (k+1)) : quietly A.val ↔ ∀ j≤k, signal j A.val=0 := by
  constructor
  · intro hs; obtain ⟨u,h,hu,hP⟩:= primitive _ _ (cabin_stor A.property) hs; intro j hj; rw [←hu,signal,LinearMap.comp_apply]; suffices he : Bare.wideLinear G j 1 (0:Cover) (momentE u)=0 by simp [he]
    simp only [Bare.wideLinear,LinearMap.smul_apply,LinearMap.sum_apply, LinearMap.comp_apply, tilted, washed, smul_zero, Finset.sum_const_zero,map_zero]
  intro H i b x
  have e (m) (hm:m≤k) (hh:∀ i b,curlK A.val i b∈Loft _ m) : leaf m (curlK A.val) = 0 := congrArg Subtype.val ((sound _ A.property hh).symm.trans (H m hm))
  have hd (m) (hm:m≤k) (hh:∀ i b,curlK A.val i b∈Loft _ m) (D:List Axis) (hD:D.length=m) (i b : Axis) : combine D (curlK A.val i b)=0 := by
    funext y
    let L:=leaf m (curlK A.val)
    have hp (q : Fin m→Axis): ((m.factorial:ℝ)⁻¹) • jumps m q (curlK A.val i b) 0=0 := by rw [← show L i b _ = _ from fertile (fun t:Fin m→Axis=> ((m.factorial:ℝ)⁻¹) • jumps m t (curlK A.val i b) 0) q]; unfold L; rw [e m hm hh]; rfl
    rw [loft_basis (loft_scoped m 0 _ (by simpa using hh i b) D hD) y]
    suffices z:∃ q:Fin m→Axis,D=List.ofFn q by obtain ⟨q,e⟩:=z; rw [e,←jumps_eq]; exact (smul_eq_zero.mp (hp q)).resolve_left (by positivity)
    exact ⟨fun i=>D.get (Fin.cast hD.symm i), by subst m; exact (List.ofFn_get _).symm⟩
  have hh : ∀ r:ℕ,r≤k → ∀ i b,curlK A.val i b∈ Loft _ r := by
    intro r hr; induction hr using Nat.decreasingInduction with
    | self=>exact fun i j=>curl_degree A i j
    | of_succ r hr ih=> exact fun i b D hD=> hd (r+1) hr ih D hD i b
  exact congrFun (hd 0 (Nat.zero_le _) (hh 0 (Nat.zero_le _)) [] rfl i b) x
end YM.RG11.FirstW
