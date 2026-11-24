import YM.MSbar.Sat.Wind
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U:Config G f}{R:Rep G f}{σ C T a v y δ w D b u Δ μ ψ t₀:ℝ}{k n:ℕ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio)(J: Voice G)(p:Palisade)
     (i:S.Choices) (j:Key F G) (t:ℝ)(m:ℕ)
set_option quotPrecheck false
local notation "N"=> (Key F G)
local notation "H"=> priced F i R.clip R.path
local notation "L"=> address F G
local notation "X"=> shutterPad F G j m
local notation "x₀"=> crown F i j t m R
local notation "h!"=> pedal F x₀
local notation "k₀"=> ice p.coords p.gap p.a p.density
variable (x:Positions (Primary c G))(h:Grants i R F p n)(g:Clear G J) (hd: S.patch.Branches S.kernel G)
local notation "T!"=> R.p.threshold
local notation "V"=> represent (tint G _ x)
local notation "Y"=>halo (2*k) X
local notation "τ"=> excavation F Y T! b
variable (hA : Floss p J t u D t₀ v b a Δ ψ m)
    (htb: necklace S.patch≤k) (hv: represent (tint G (Exterior.Body 1 c) x) ∈ calm G c v) -- notation quote fails
    (hx: ‖x‖ ≤ a)(hb: bonfire F G (halo (2*k) (shutterPad F G j m)) (J.C*D) u≤ t₀)
variable {cF : ℝ} (hu:U∈excavation F (halo (2*k) (shutterPad F G j m)) R.p.threshold b)
set_option quotPrecheck false
local notation "W"=> chink F J V U Y
local notation "W'"=> chink F J V (pedal F (crown F i j t m R) U) Y
local notation "U!"=> exterior F J V U Y
local notation "V!"=> exterior F J V (pedal F (crown F i j t m R) U) Y
include hd h hA g hx hv hu hb htb
-- all pre V and witness.This regulator for weighted.A.Duty
variable (ρ:ℝ) (hy:Quasi R.eval ρ) (sold:Admitted (represent (tint G (Exterior.Body 1 c) x)) R S σ C δ T w)(hz:0≤ R.beta) -- Amb notation
include sold hz
def hurry (p:Palisade)(A X₁ D:ℝ) :=
   let j:=p.coords*countCost p.a
   X₁*(X₁*(p.density*j)+A*(p.density*j)*j*A)+ D*(A*(p.density*j)+A*(p.density*j)*j*A)
local notation "i!"=> R.beta
include hy
lemma budgetPress : boundPress S R V U ≤ Real.exp (ρ*(J.C*u)*(4*↑(X).card)+R.beta*(Δ*p.noise))*boundPress S R V (h! U):=by
   obtain ⟨ht,hq⟩:= embossed F J p i j t m x h g hd hA htb hv hx hb hu
   let Xp:= board F X; let P:= Xp.image (fun i:F.Free=>i.val); have he':S.density (i!) (h! U) V ≥ 0:=sold.kernel.positive _ _
   have hh: -R.beta*sigh S i V U! V! ≤ R.beta * (Δ*p.noise):=by linarith only [mul_le_mul_of_nonneg_left (abs_le.mp hq).1 hz]
   have he: R.eval U ≤ Real.exp (ρ*(J.C*u)* P.card)*R.eval (h! U):= Quasi.assemble hy P ?_ ?_
   · unfold boundPress; rw [ht]; refine (mul_le_mul he (mul_le_mul_of_nonneg_left (Real.exp_monotone hh) he') (mul_nonneg he' (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (hy.positive _))).trans ?_; rw [Real.exp_add]
     have hp : (P.card:ℝ) ≤ 4*((X).card:ℝ):=by rw [mul_comm]; exact_mod_cast card_image_le.trans (boardC F X)
     have ha₀:0 ≤ ρ*(J.C*u):= mul_nonneg hy.cost (mul_nonneg (zero_le_one.trans g.cost) hA.warmth)
     apply le_trans ?_ (le_of_eq (show (Real.exp (ρ*(J.C*u)*(4*↑(X).card))*R.eval (h! U))*(S.density (i!) (h! U) V*Real.exp (R.beta*(Δ*p.noise))) = _ from by ring))
     exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left hp ha₀)) (hy.positive _)) (mul_nonneg he' (Real.exp_pos _).le)
   · intro q hq -- i overwritten; adjust
     unfold pedal; by_cases hg:q∈ F.trunks
     · rw [show F.drape _ q=1 from F.on_tree _ ⟨q,hg⟩]; group
     let k:F.Free:=⟨q,hg⟩; have he:x₀ k=1:=by by_contra hp; apply hq; exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ k,pages F i j t m _ hp⟩)
     rw [show F.drape _ q= 1 from (F.off_tree _ k).trans he]; group
   intro q h'
   obtain ⟨k,hk,rfl⟩:= mem_image.mp h'
   let f:= braid F i j t m R k; have hm : ‖f‖≤u:=(masts F p i j t m h k).trans hA.frock
   have hp : pedal F x₀ U k.val=(F.foldAt U k.val.1)⁻¹*G.lieExp f*F.foldAt U k.val.1 *U k.val :=by rw [pedal,Forest.off_tree]; rfl
   change G.chord (U k.val* _ ) ≤ _; rw [hp]; let b:= (F.foldAt U k.val.1)⁻¹
   rw [show U _ * _ = b*(G.lieExp f)⁻¹ * b⁻¹ from (by unfold b; group),G.chord_conj,G.chord_inv]; exact ((g.small f (hm.trans (hA.step.trans hA.roll))).2).trans (mul_le_mul_of_nonneg_left hm (zero_le_one.trans g.cost))
omit hy
-- Pose strong.S.outset small.
local notation "Q!" => hurry p (max a D) Δ ψ
local notation "A!" => outset R.p σ C δ T R.beta k (X).card
lemma whirlwind {v₀:ℝ} (hU:(pedal F (crown F i j t m R) U)∈excavation F (halo (2*k) (shutterPad F G j m)) R.p.threshold b) (hB:R.p.B ≤ k)(hQ: WilsonStartup.Decent R.clip R.p)(hm:v₀ ≤ t*(fareX F J V U j.1 j.2- vest (priced F i R.clip R.path) x j)) :
    S.density R.beta U V * Real.exp (R.exponent U) ≤ Real.exp (A!+R.beta*(Q! - v₀))*S.density R.beta (h! U) V* Real.exp (R.exponent (h! U)):=by
    obtain ⟨hs,hq⟩:= embossed F J p i j t m x h g hd hA htb hv hx hb hu
    obtain ⟨hM,r,r',-,hχ⟩:= thistle F J p i j t m x h g hA htb hv hx hb hu
    let Yp:=canoe (S:=S) F (h! U); let Xp:=canoe (S:=S) F U
    have hT:Place X k Xp U! Yp V! T!:=⟨hM.from_old,hM.renewed,hM.approves,hM.afterR, show Healthy _ Y Xp from (by unfold Xp canoe Healthy; rw [gauge_flags];exact hu.1), show Healthy _ Y Yp from (by unfold Yp canoe Healthy; rw [gauge_flags]; exact hU.1)⟩
    let D:= (A!) + R.beta*(Q! - v₀); have hP := formal_edge hT sold.lawful hB hQ hz
    let P:= priced F i R.clip R.path; let T₀:= t* (fareX F J V U j.1 j.2-vest P x j); have hK :(P (meetVar x W')-P (meetVar x W)) ≤ Q! - v₀:=by
       have hx' := steer (f:=P) h.buys r r' (lt_of_lt_of_le hA.safe p.enroll) j hχ
       rw [add_sub_cancel, show W j= fareX F J V U j.1 j.2 from ?_] at hx';
       · change _ ≤ hurry p (max a _) Δ ψ - v₀; have hq:= (abs_le.mp hx').2; unfold hurry; linarith only [hq,(show v₀≤ _ from hm)]
       let p:= j.fst; have hh:p∈board F Y:=Finset.mem_filter.mpr ⟨mem_univ _,halo_subset _ _ (halo_spec.mpr ⟨p.val.1,mem_singleton_self _,separation_self _ ▸ Nat.zero_le _⟩)⟩
       change tint G _ W p j.2 = _; rw [chink, ContinuousLinearEquiv.apply_symm_apply]; dsimp only; rw [if_pos hh]
    have hp : -R.beta*sigh S i V U! V! + R.exponent U ≤ D + R.exponent (h! U):=by
       unfold P at hK; rw [written,written] at hK; have hE (μ) : R.exponent (canoe (S:=S) F μ)=R.exponent μ:= Further.DenseMixedKernels.Throng.phase sold.lawful _ _
       unfold Xp Yp at hP; rw [hE,hE] at hP
       unfold tested at hK; unfold sigh exterior at *; unfold D
       linarith only [(abs_le.mp hP).2,mul_le_mul_of_nonneg_left hK hz]
    rw [hs,mul_assoc,mul_comm (Real.exp ((A!)+R.beta*(_-v₀))) (S.density ..),mul_assoc,←Real.exp_add,←Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone hp) (sold.kernel.positive _ _)
end YM.MSbar.Heath
