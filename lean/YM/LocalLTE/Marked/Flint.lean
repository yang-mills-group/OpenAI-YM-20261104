import YM.LocalLTE.Marked.Premium
import YM.MergeProof.Emit
/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt


open Merge Merge.Palette Height Daisy Lotus
-- every factor still selected independently.R.indices attached later. purposes geometry active.Down.
variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf R)(rA:ι→ℝ)(he:∀ i, 0≤rA i)
set_option quotPrecheck false
local notation "χz"=> Merge.Palette.sign M S
local notation "τ"=> Merge.Tickets (Merge.Palette.sign M S)

-- bet costs on multiselects and draw routes. Prove zero off.R.
-- TERR Bayesian.
abbrev Oscars (M:ι→Lotus.Leaf R) (p : Clusters H.ThinP) := Option (Fin p.fst)→Merge.Tickets (Merge.Palette.sign M S)
variable (D:Oscars M p)
def wingTerm (U:Config G c) :ℝ:= let _ := H; coefficient H.seam p.2 * (∏ i,(waltz H χ M (p.2 i) (D i)) U) /↑(p.fst+1).factorial
-- no amplitudes. Carry global r weights.Ext.
abbrev winhit (i:H.ThinP)(Q: Tickets (Merge.Palette.sign M S)):= 2^j*inlet N M i.val Q
def wingBill:= |coefficient H.seam p.2| * (∏ i, winhit N M (p.2 i) (D i))/↑(p.fst+1).factorial
-- Zero if tickets fail.Owner pays.
def wife (n:ℕ):= (shiftG s*(1+coverNumber (radiusB s) (reachability (H:=H) p)))^(n*j)*wingBill N p M D
include N
local notation "P'"=> wingTerm (χ:=χ) p M D
variable (h':HostQ H N.conduit A B k)
omit [Fintype ι] in
lemma fareV : 0 ≤ wingBill N p M D:= div_nonneg (mul_nonneg (abs_nonneg _) (prod_nonneg fun i _=> mul_nonneg (show 0 ≤ (2^j:ℝ) by positivity) (inlet_nn ..))) (by positivity)
-- amplitude.Bank
include h'
omit [Fintype ι] in
lemma wing (Z:BudgetPoint)(ht:Z.threshold=Pressure.temp s)(hp:Z.order≤j)(n:ℕ)(hn:Z.power≤n):
    let X:= reachability (H:=H) p
    ((fun U=>coefficient H.seam p.2*(∏ i, Merge.Palette.act M H χ U (p.2 i).val (D i)) /↑(p.fst+1).factorial)= masked Z.threshold X (wingTerm (χ:=χ) p M D)) ∧ Z.Regular X P' ∧ ∀ o∈X, Z.supBounds o X P' (wife N p M D n):=by
    intro X; let f i:= waltz H χ M (p.2 i) (D i); let Y i := H.smallAt (p.2 i); let a:=coefficient H.seam p.2 /↑(p.fst+1).factorial
    let g i:=inlet N M (p.2 i).val (D i); have hv i: 0≤g i:=inlet_nn N M (D i) _
    have h i V:= vivid N M V (D i) (p.2 i) h'
    have hl U:P' U=a*∏ i,f i U:=by unfold wingTerm a f; ring
    have hY i: Y i ⊆ X:= subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ _)
    have hF V (hV:Healthy Z.threshold X V): Ore V P' v (wingBill N p M D) j := by
       intro E _ _ _ U x he hB
       rw [ht] at hV
       have hh := Brush.all_prod univ (fun i t=> f i (U t)) g (fun _=>1) (fun i _=> ((h i V).2.2.2.2 (Finset.disjoint_of_subset_left (hY i) hV)) E U x he hB)
       simp_rw [Function.comp_def,hl]; apply (hh.trim.smul a).climb _ le_rfl
       simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]
       unfold wingBill; let e:= coefficient H.seam p.2;change ‖a‖*((∏ i,g i)*(1+((p.fst+1:ℕ):ℝ))^j) ≤ |e| *(∏ i,2^j*g i)/_
       conv_rhs => rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
       have he : (1+((p.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(p.fst+1) := by
          rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=p.fst+1)
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Finset.prod_nonneg fun i _=>hv i)) (norm_nonneg a)).trans_eq
       unfold a e; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ ((p.1+1).factorial:ℝ))]; ring
    have hk : LocalOn X P' := by
       intro u w hu; rw [hl,hl]; exact congr_arg _ (prod_congr rfl fun i _=> (h i 1).2.1 u w (agrees_mono hu (Finset.coe_subset.mpr (hY i))))
    have hh (V) (hV : Healthy Z.threshold X V) : ContDiffAt ℝ (↑Z.order) (P' ∘ increment V) 0:= (charted (hF V hV) N.position).of_le (Nat.cast_le.mpr hp)
    have ha:Sailor G Z.threshold q j:=⟨fun c _ hb=> N.weigh.stroke _ _ (hb.trans (ht.trans_le N.talent))⟩
    refine ⟨?_,⟨hk,?_, ?_, hh, fun U hU A l hl=> left_has A hl (hh U hU)⟩,fun x hy=>?_⟩
    · funext U; simp_rw [(fun i=> (h i U).1),ht]; by_cases hV:Healthy (Pressure.temp s) X U; swap
      · rw [masked_ne _ _ _ _ hV]; obtain ⟨x,hx,hb⟩:=Finset.not_disjoint_iff.mp hV; obtain ⟨i,hi,hp⟩:= Finset.mem_biUnion.mp hx; rw [Finset.prod_eq_zero hi (masked_ne _ (Y i) _ _ (Finset.not_disjoint_iff.mpr ⟨x,hp,hb⟩)),mul_zero,zero_div]
      rw [masked_eq _ _ _ _ hV]; simp_rw [(fun i=> RG.masked_eq _ (H.smallAt (p.2 i)) (waltz H χ M (p.2 i) (D i)) _ (Finset.disjoint_of_subset_left (hY i) hV))]; rfl
    · rw [funext hl]; exact measurable_const.mul (Finset.measurable_fun_prod _ fun i _=> (h i 1).2.2.2.1)
    · intro z U; rw [hl,hl]; exact congr_arg (a*·) (prod_congr rfl fun i _=> (h i U).2.2.1 z U)
    let D' := radiusB s; let b:ℝ := coverNumber D' X; let Y':= shiftG s*(1+b)
    have ht':0≤ b := Nat.cast_nonneg _; have hi: 1≤Y' := one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB s)]) (le_add_of_nonneg_right ht')
    refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans hi) _) (fareV N p M D), fun U hU l hl hq=>?_⟩
    apply (costsD (g:=P') hk ha N.income x _ N.near (hF U hU) (Y:=Y') ?_ hi l (hl.trans hp) hq).trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hi (Nat.mul_le_mul_right j hn)) (fareV N p M D)))
    intro y hp; have hf : (separation y x:ℝ) ≤ b*(4*(D':ℝ)+2)+2*(D':ℝ):=by unfold b; exact_mod_cast Corona.extent X D' hp hy
    unfold Y' shiftG; change _ ≤4*(2*(D':ℝ)+1)*(1+b); nlinarith [Nat.cast_nonneg (α:=ℝ) D']
omit N h'
def pearl (D:Oscars M p) := ∏ i,∏ j∈ (D i).val,rA j
include N
lemma creditU : (∑ z:Oscars M p, pearl p M rA z * wingBill N p M z)=slideΖ N M rA p:=by
    unfold pearl wingBill slideΖ clusters
    let e:= |coefficient H.seam p.2|; let f i z:= (∏ j∈(z:Merge.Tickets χz).val, rA j)*winhit N M (p.2 i) z
    have hV (z:Oscars M p): (∏ i:Option (Fin p.fst),∏ j∈(z i:Merge.Tickets χz).val, rA j)*( e*(∏ i, winhit N M (p.2 i) (z i))/↑(p.fst+1).factorial) = e*(∏ i,f i (z i))/↑(p.fst+1).factorial:=by simp only [f,prod_mul_distrib]; ring
    have he i: pier N M rA (p.2 i)=∑ z:Merge.Tickets χz,f i z:=by
       unfold pier; rw [← points N M rA, mul_sum]; exact Finset.sum_congr rfl (fun z _=>mul_left_comm ..)
    change ∑ z: Oscars M p,(∏ i:Option (Fin p.fst),∏ j∈(z i:Merge.Tickets χz).val, rA j)*( e*(∏ i, winhit N M (p.2 i) (z i))/↑(p.fst+1).factorial)=_
    simp_rw [hV]; rw [← Finset.sum_div,← Finset.mul_sum,← Fintype.prod_sum]; simp_rw [he] -- normalization instances.M
    rfl
-- helper use star.
lemma debtU (n:ℕ) : (∑ z:Oscars M p, pearl p M rA z * wife N p M z n)=markU N M rA p n:=by
    unfold wife markU; rw [← creditU]; exact Eq.symm <| (mul_sum ..).trans (sum_congr rfl (fun i _=> mul_left_comm ..))
end Captain
end YM.ConnectedActivityE6.Blaze.March
