import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Chunk
/-!
# Also G.1 when s<r (compact ratios). From **only** our prior purchases, no smoothness in r.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale Quotes
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {W W' : ℝ} {I : Type*} {X : Filter I} {η T r : I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
local notation "home" => fun (_:I)=>(1:ℝ)
variable {d : ℕ}
lemma local_cash {u:I→ℂ}{h:I→ℝ} (c:Fare home X h u) : u=O[X] h := by obtain ⟨p,H⟩:= c; simpa [logs] using H
-- crop of identity frame and identity clock
private lemma pacing {p:ℕ} (hp:0< (p:ℕ))(t:ℝ) : crop p t PowerSeries.X=(t:ℂ) := by
  rw [crop_apply,Finset.sum_eq_single 1]
  · simp
  · intro i _ hi; rw [ coeff_X ]; split_ifs with h <;> first| contradiction|simp_all
  simp [Finset.mem_range]; omega
include H in
private lemma conversion_flat : conversion B 0 d=1 := by unfold conversion; rw [ (H.toTouched.ground).2, Level.flat,map_one,mul_one ]
private lemma crop_home (i j : Toon G d) (p:ℕ) (t:ℝ) : crop p t (prose 1 i j)=(1:Operator G d) i j:= by
  rw [ ← sum_coords 1]; simp_rw [coeff_one,smul_ite ]; simp [Finset.sum_ite_eq',Finset.mem_range] 
  exact congr_arg (fun p:Operator G d => p i j) one_matrix
private lemma mul_cost {w v:I→ℝ} {F D:I→Operator G d} (hf:(stiffness∘F)=O[X] w) (hd: (stiffness∘D)=O[X] v) : (fun i=> stiffness (F i * D i))=O[X] (fun i=> w i*v i) := by
  apply IsBigO.trans ?_ (hf.mul hd)
  apply IsBigO.of_bound'; refine Eventually.of_forall fun i=>?_ ; simp only [Function.comp_apply]; rw [Real.norm_of_nonneg (stiffPos _),Real.norm_of_nonneg (mul_nonneg (stiffPos _) (stiffPos _))]; exact stiffMul ..

variable (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[late] (g0 G)) {D : Route G} (hD : Balances D) (h' : selfCharge D) (P : StepCost G R B t D)
    (hr : Tendsto r X late) (hT : ∀ᶠ i in X,T i ∈ Icc 1 W)

local notation "g" => g0 G ∘ r
local notation "s" => (fun i:I=>r i*T i)
local notation "g'" => g0 G ∘ s
local notation "α" => t∘r
local notation "τ" => t∘s
local notation "η'T" => fun i:I=> Real.log (T i)
include hG H ht hr hT hD h' P
lemma compact_opposed (p:ℕ)(hp:0<p) : (fun i=> stiffness (columns (D (s i) (r i) d)- columns (accepts (conversion B (η'T i) d) p (τ i))))=O[X] (fun i=>g0 G (s i)^(p+1)) ∧
    (fun i=> (α i:ℂ)-crop p (τ i) (R (η'T i)))=O[X] (fun i=>g0 G (s i)^(p+1)) := by
  obtain ⟨M,Y⟩:= chunk H hG ht hD P hr hT p d
  obtain ⟨c,C₀,K⟩:= upper_uniform hG hr hT
  have hu := ht.comp_tendsto hr
  have ht' : Tendsto t late (𝓝 0) := ht.trans_tendsto (g0_zero hG)
  have ha := (ht'.comp hr |>.abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)| < 1))
  have hc := (ht'.comp c |>.abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)| < 1))
  have hz := ( (g0_zero hG |>.comp hr).abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)| < 1))
  have hx : ∀ᶠ i in X, η'T i∈Icc 0 (Real.log W) := hT.mono fun i ⟨h,z⟩ => ⟨ Real.log_nonneg h, Real.log_le_log (by linarith) z ⟩
  have y := C₀.pow (p+1); let gQ i := g i^(p+1)
  let Q i:=conversion B (η'T i) d; let Q' i:= Reg.Point.stepV (R (-(η'T i))) (Q i)
  let Z i:= accepts (Q i) p (τ i); let A i:= D (r i) (s i) d; let E i:= D (s i) (r i) d
  let root (i:I) := H.led (-(η'T i)) |>.start
  have V: Notes X home α g p home Z Q':= by
    intro i j; simp_rw [Q',prose_subst _ _ (root _)]; exact Coin.substitute hu ha (Eventually.of_forall fun _=>le_refl (1:ℝ)) hc Y root (Notes.for_crop (poles_compact H _ isCompact_Icc hx) i j)
  constructor
  · have hc : (fun i=>stiffness (columns (A i)*columns (Z i)-1)) =O[X] gQ := by
      refine matrixPay.mpr fun i j=>?_ ; have h:= local_cash ((Notes.product hu ha hz (Eventually.of_forall fun _=>le_refl (1:ℝ)) M V i j).expense)
      refine h.congr (fun k=>?_) (fun k=>by unfold gQ; simp)
      change columns (A k * Z k) i j - crop p (α k) (prose (conversion B (-Real.log (T k)) d * Reg.Point.stepV (R (-Real.log (T k))) (conversion B (Real.log (T k)) d)) i j)=_; rw [ ← composed H, neg_add_cancel, conversion_flat H, crop_home]; change _ = (columns (A k)*columns (Z k)) i j-_; rw [composition']; rfl
    have L i : columns (E i)*columns (A i)=1 := by rw [composition',show E i ∘ₗ A i=_ from (hD (s i) _ (s i) d).symm,h',one_matrix]
    have hf : (fun i=> stiffness (columns (E i)))=O[X] home := (issued_norms H hG ht (by exact zero_lt_one) hD P hr (into_budget hG hr hT) h').2
    change _=O[X] _; exact (((mul_cost hf hc).congr_right (fun i=>one_mul _)).congr_left (fun i=> by rw [mul_sub,← mul_assoc, L,one_mul,mul_one]; unfold stiffness; change _=∑ j, ∑ k, ‖columns (E i) j k - columns (Z i) j k‖; simp_rw [Matrix.sub_apply]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun i _=> norm_sub_rev .. )).trans y
  have h := local_cash ((Coin.substitute hu ha (Eventually.of_forall fun _=>le_refl (1:ℝ)) hc Y root (Coin.already (ψ_compact H isCompact_Icc hx))).expense)
  apply IsBigO.trans _ y; apply h.neg_left.congr (fun i=>?_) (fun i=>mul_one _)
  change -(crop p (τ i) (R (η'T i))-crop p (α i) ((R (η'T i)).subst (R (-(η'T i)))))= _; rw [← (H.additive ..).1, neg_add_cancel,(H.toTouched.ground).1,pacing hp,neg_sub]
  -- sign negative for target
end YM.FVA2.GradedFar259.ScaleCost
