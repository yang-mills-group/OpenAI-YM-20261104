import YM.MSbar.Heath.Charts
import YM.MSbar.Rolling.Stays
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push Pressure
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
-- bounds use energy_+. note reused native.
local notation "G!"=> G.chord
local notation "E₀"=> Wilson.energy
local notation "Γ!"=> Real.exp
variable (a:ℝ)(ha:0<a)
noncomputable def quota (S:StepData c f) (U:Config G f)(V:Config G c)(t:S.Choices) (a:ℝ) := Real.sqrt (a*Wilson.energy U +noiseTaylor S V U t)
open Heath Finset
lemma coast(G:Gauge)(i:G.El) : 0 ≤ G.price i:=by linarith only [G.chord_price i,sq_nonneg (G.chord i)]
variable (U:Config G f)(V:Config G c)(t:S.Choices)
include ha
lemma quarrel : let q:= quota S U V t a
    q^2= a*Wilson.energy U+noiseTaylor S V U t:= by intro q; have hh:0 ≤ noiseTaylor S V U t := mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun i _=>coast G _); exact Real.sq_sqrt (add_nonneg (mul_nonneg ha.le (Finset.sum_nonneg fun i _=>coast G ..)) hh)
private lemma vitality (p:Face (Per f)): G.chord (faceValue U p) ≤ Real.sqrt (2/a)*quota S U V t a:=by
    let w:= quota S U V t a; have hx:w^2=a*Wilson.energy U+noiseTaylor S V U t:=quarrel a ha U V t
    have hy:0≤ noiseTaylor S V U t:=mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun i _=>coast G _); have h : a*G.price (faceValue U p) ≤ w^2:= (mul_le_mul_of_nonneg_left (show G.price (faceValue U p) ≤ Wilson.energy U from Finset.single_le_sum (f:=fun j=> G.price (faceValue U j)) (fun _ _=> coast G _) (Finset.mem_univ _)) ha.le).trans (hx.symm ▸ (le_add_of_nonneg_right hy)); apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp; rw [mul_pow,Real.sq_sqrt (by positivity:0≤2/a),G.chord_price]; change _≤2/a*w^2; rw [show 2/a*w^2=2*w^2/a from (by ring),le_div_iff₀ ha]; linarith only [h]
lemma words (i:Bond c) : wire (S.prediction U t) V i ≤ Real.sqrt (2/S.kernel.penalty)*quota S U V t a:=by
    let k:= S.kernel.penalty; let r:= fun i : Bond c=> G.price (V i * (S.prediction U t i)⁻¹); let w:= quota S U V t a; have hp :0<k:=S.kernel.penalty_pos; have hx:=quarrel a ha U V t; have he:k*r i ≤ w^2 :=(mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=r) (fun _ _=>coast G _) (Finset.mem_univ _)) hp.le).trans (le_trans (le_add_of_nonneg_left (mul_nonneg ha.le (Finset.sum_nonneg (s:=Finset.univ) (f:=fun j:Face (Per f)=>G.price (faceValue U j)) fun _ _=>coast G _))) hx.symm.le)
    apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp; change G.chord _ ^2 ≤ (Real.sqrt (2/k)*w)^2; rw [mul_pow,Real.sq_sqrt (by positivity:0≤2/k),G.chord_price,show 2/k*w^2=2*w^2/k from (by ring),le_div_iff₀ hp]; change (2*r i)*k≤_; linarith only [he]
-- common.V energy & earth
noncomputable def macroQ (S:StepData c f)(a:ℝ) := HealthBox S *Real.sqrt (2/a)
where HealthBox (S:StepData c f) := ((box (macroR S.patch)).card:ℝ) * Fintype.card PlaqAxes
local notation "q!"=> quota S U V t a

lemma portCap (x:Site c): port S x U ≤ macroQ S a*quota S U V t a:= by
   apply (Work.E01.port_le S U x (Real.sqrt (2/a)*q!) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (fun i _=> vitality a ha U V t i)).trans_eq; unfold macroQ macroQ.HealthBox; ring
variable (S)
lemma shed (G:Gauge) :∃ L:ℝ, 0 ≤ L∧ ∀ (U:Config G f)(V:Config G c)(t:S.Choices),0<S.likelihood U t → Wilson.energy V ≤ L*quota S U V t a^2:=by
    obtain ⟨C,hC,hT⟩:= qdc G S.kernel S.patch.J
    let A:= Real.sqrt (2/S.kernel.penalty); let B:= C/(S.patch.L.val:ℝ)^2; let k:= 4*A+B*macroQ S a; refine ⟨Fintype.card (Face (Per c))*k^2,by positivity,fun U V t hh=>?_⟩
    let Q:= quota S U V t a; let ft:= k*Q; let T:= S.prediction U t
    have hx(j): port S j U ≤ macroQ S a*Q := portCap a ha U V t j -- pin
    have ht(j:Face (Per c)): G.chord (faceValue V j) ≤ ft:=by
        let H:=B; apply (hT c _ S rfl rfl U V j.1 t (wraps S t hh j.1) j.2).2.trans -- fS rename
        have hh(i:Bond c): Pressure.wire T V i ≤ A*Q:=words a ha U V t i; apply le_trans (add_le_add (b:=4*A*Q) ?_ (mul_le_mul_of_nonneg_left (hx j.1) (by positivity))) _
        · unfold Pressure.fuel; refine (add_le_add (add_le_add (add_le_add (hh _) (hh _)) (hh _)) (hh _)).trans_eq ?_; ring
        unfold ft k B; exact le_of_eq (by ring)
    refine (Finset.sum_le_sum (s:=Finset.univ) (f:=fun j:Face (Per c)=> G.price (faceValue V j)) (g:=fun _=> k^2* Q^2) (fun i _=>?_)).trans_eq ?_
    · have hg:= pow_le_pow_left₀ (G.chord_nonneg _) (ht i) 2; rw [show ft=k*Q from rfl, G.chord_price,mul_pow] at hg; linarith only [hg,coast G (faceValue V i)]
    rw [sum_const, Finset.card_univ,nsmul_eq_mul]; ring
end YM.MSbar.Rolling
