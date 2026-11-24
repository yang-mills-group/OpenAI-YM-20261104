import YM.MSbar.Rolling.Rate
import YM.MSbar.Rolling.Orb
import YM.MSbar.Sat.Probe
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set
open Next.SectorChange Push Push.Uniform
open RG Lattice Wilson Precision Tree Metric Pressure
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{c f:Side}{S: StepData c f}
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
open Heath Price
local notation "L"=> YM.MSbar.Rolling.fuel
-- exponent cap Z threshold; amplitude.E.HighPay
lemma road (p q:ℕ)(N:ℕ) (hz:0< N) (hn:p<2*N): ∀ᶠ t:ℝ in Γ, Real.exp (L t ^ p-L t^(2*N))/ t ^ q ≤ t^q:=by
    filter_upwards [width,awake.eventually_ge_atTop (4:ℝ),awake.eventually_ge_atTop (4*(q:ℝ))] with t ⟨ht,hT,hf⟩ hh he
    rw [div_le_iff₀ (pow_pos ht _),← Real.log_le_log_iff (Real.exp_pos _) (by positivity), Real.log_mul (pow_ne_zero _ ht.ne') (pow_ne_zero _ ht.ne'),Real.log_exp,Real.log_pow] -- inspect
    let a:= L t; have hk: Real.log t= -a:=by unfold a Rolling.fuel; rw [Real.log_inv,neg_neg]
    have hA : 2 * a^p ≤ a^(2*N):= by have hg:2≤ a:=by linarith
                                     have hh: a^(p+1) ≤ a^(2*N):=pow_le_pow_right₀ hf hn; rw [pow_succ] at hh; exact le_trans (by rw [mul_comm]; gcongr) hh
    have hC : 4*(q:ℝ)*a ≤ a^(2*N):= (mul_le_mul_of_nonneg_right he (zero_le_one.trans hf)).trans (sq a ▸ (pow_le_pow_right₀ hf (show 2 ≤ 2*N by omega)))
    rw [hk]; change a^p - a^(2*N) ≤ _; linarith only [hC,hA]
variable (J:Voice G)(B: Forest S.ratio)(a:ℝ)(h:Serves S G)(ha:0<a)(hJ:Clear G J)
local notation "X"=> Positions (Primary c G)
local notation "Y"=> Positions (Key B G)
def yard (p:ℕ) {E:Type*}[Norm E] (x:ℝ)(y:E) := ‖y‖ ≤ Rolling.fuel x ^ p
noncomputable def postcard (G:Gauge) (n:Side)(s:ℝ)(v:Positions (Primary n G)):= represent (tint G _ (s•v))
abbrev CoverQ(U:Config G f)(t:ℝ)(x:X)(i:S.Choices) := quota S U (postcard G c t x) i a
local notation "E!"=>CoverQ a
include h hJ ha
lemma exteriorR (n:ℕ)(m:ℕ)(hm:n≤ m) : let A(t:ℝ):= Rolling.fuel t ^(m+1)
    ∀ᶠ t in Γ, ∀ (x:X)(U:B.Slice G)(i:S.Choices), ‖x‖ ≤ Rolling.fuel t ^ n → U∉ urn (A t) t→ 0<S.likelihood (B.drape U) i→ t * Rolling.fuel t ^ m ≤ CoverQ a (B.drape U) t x i:=by
    intro A; let X₀:= compass S.patch S.kernel G; let e:=X₀*macroQ S a+Real.sqrt (2/S.kernel.penalty); let W:= J.C*shade G; let W':= W+e; let P(x:ℝ):= x*Rolling.fuel x^m; have hp:P= P:=rfl
    have hT:= subs m; filter_upwards [width,(((show Tendsto P Γ _ from hT).const_mul (shade G)).eventually (eventually_lt_nhds (show shade G*0 < J.r by rw [mul_zero]; exact hJ.depth))),((show Tendsto P Γ (𝓝 0) from hT).const_mul W').eventually (eventually_lt_nhds (show W'*0 < J.δ from by rw [mul_zero];exact hJ.dist)),awake.eventually_ge_atTop (J.C*W')] with t ⟨hx,hB,hG⟩ hh hH hR x U i hx' hh' he
    let V:= postcard G c t x; let D:=B.drape U; let Q:= CoverQ a D t x i; let k:= P t
    refine le_of_not_gt (fun ht=>?_); apply hh'
    have hC:0≤ J.C:= zero_le_one.trans hJ.cost; have hK:0≤k:= by unfold k P; positivity
    have hv(j:Edge (Site c)):G.chord (V j)≤ W*k:=by
        unfold V postcard; rw [Work.F03.represent_link]; let z:=tint G (Exterior.Body 1 c) (t•x); have hw(i:Exterior.Body 1 c) : ‖z i‖ ≤ shade G*k:=by
             apply (norm_le_pi_norm _ _).trans ((tint_le _).trans _); apply mul_le_mul_of_nonneg_left _ (shade_pos G).le; rw [norm_smul,Real.norm_of_nonneg hx.le]; exact mul_le_mul_of_nonneg_left (hx'.trans (pow_le_pow_right₀ hG hm)) hx.le
        exact ((hJ.small (z _) ((hw _).trans hh.le)).2).trans ((mul_le_mul_of_nonneg_left (hw _) hC).trans_eq (mul_assoc ..).symm)
    have hD(j:B.Free) : G.chord (U j) ≤ W'*k:=by
        let q:= S.ratio.parent j.val.1; let P:= S.prediction D i; let r:=Precision.replica S.ratio V j.val
        have H: G.chord (U j*r⁻¹) ≤ e*k:=by
             rw [← B.off_tree U j]; have hp' := (Work.E02.answer G S.patch.L S.patch.J S.kernel).choose_spec.2 c f S rfl rfl rfl h.thick.2.1 h.thick.2.2 B D (fun _ hb=> B.on_tree _ ⟨_,hb⟩) V j.val i (Pressure.wraps S i he q); have ht' : Real.sqrt (2/S.kernel.penalty)*Q ≤ Real.sqrt (2/S.kernel.penalty)*k:= mul_le_mul_of_nonneg_left ht.le (Real.sqrt_nonneg _); have hh : X₀*port S q D ≤ X₀*(macroQ S a)*k:=by
                  have hh:0 ≤ macroQ S a:=by unfold macroQ macroQ.HealthBox; positivity
                  exact (mul_le_mul_of_nonneg_left ((portCap a ha D V i q).trans (mul_le_mul_of_nonneg_left ht.le hh)) ((weather_pos G S).le)).trans_eq (mul_assoc ..).symm
             apply hp'.trans; unfold e; rw [add_mul]; apply add_le_add hh _; split; exact mul_nonneg (Real.sqrt_nonneg _) hK; exact (words a ha D V i _).trans ht'
        have hr:G.chord r ≤ W*k:=by unfold r Precision.replica; split; rw [G.chord_one]; exact mul_nonneg (mul_nonneg hC (shade_pos G).le) hK; exact hv _
        let u:= U j; have hw:G.chord u ≤ G.chord (U j*r⁻¹)+ G.chord r:=by unfold u; nth_rw 1 [show U j=U j*r⁻¹*r by simp]; exact G.chord_triangle ..
        exact hw.trans ((add_le_add H hr).trans_eq (by unfold W'; ring))
    let S'(i:B.Free):= J.decode (U i); have hP(i:B.Free): G.lieExp (S' i)=U i∧ ‖S' i‖ ≤ J.C*W'*k:=by
        obtain ⟨-,hL,ho⟩:=hJ.near (U i) ((hD i).trans hH.le); exact ⟨hL,ho.trans ((mul_le_mul_of_nonneg_left (hD i) hC).trans_eq (mul_assoc ..).symm)⟩
    let w:Y:=t⁻¹ • tape.symm (S' : LogArray G B.Free); have hM:tape (G:=G) (t•w)=S':=by unfold w; rw [smul_inv_smul₀ hx.ne', tape.apply_symm_apply]; -- charge π.norm
    refine ⟨w, Metric.mem_closedBall.mpr ?_,?_⟩
    · rw [dist_zero_right]; apply le_of_mul_le_mul_left _ hx; rw [← Real.norm_of_nonneg hx.le,← norm_smul, Real.norm_of_nonneg hx.le] -- rewrites lhs both hx. residual.
      refine (pi_norm_le_iff_of_nonneg (show 0≤ t*A t from by change 0 ≤ t* _ ^_; positivity)).2 fun i=>?_
      have hv: (t•w) i= S' i.1 i.2:= congr_arg (fun f: B.Free→G.Color=> (f i.1) i.2) hM
      rw [hv]; exact (PiLp.norm_apply_le _ _).trans ((hP _).2.trans ((mul_le_mul_of_nonneg_right hR hK).trans_eq (by unfold k P A; ring)))
    unfold kerf; rw [hM]; ext1 i; rw [show release _ _ i=_ from rfl]; change G.lieExp (S' i)*1=U i; rw [mul_one]; exact (hP i).1
end YM.MSbar.Rolling
