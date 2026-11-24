import YM.MSbar.Geneva.Snow
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{A:ι→BudgetPoint}{φ:Filter ι}(hX:Tendsto X φ atTop)
variable (P:Patch)(K:KernelChoices)(J:Voice G)
variable {α:ℝ}{n:ι→Side}(H:Stage)
-- volume shell. constraint n ~ log.W^4 minimum.
include hX
noncomputable def brimT (q:ℕ)(x:ℝ): ℝ := Real.log x^ (2*q)
omit hX in
lemma sizeL(i:Side) : Midpoint.size i=(i.val:ℝ)^10:=by unfold Midpoint.size; rw [site_card,Nat.cast_pow];ring
variable (hn:∀ᶠ i in φ,(hatW (X i))^4 ≤ (n i).val)
include hn
lemma cells : ∀ᶠ i in φ,0 < X i ∧ radiusB (X i)>0 ∧ Real.log (X i) ≥ 1∧
               100000*(radiusB (X i))^3 < (n i).val :=by
     filter_upwards [hn,(Real.tendsto_log_atTop.comp hX).eventually_ge_atTop 2000000,hX.eventually_gt_atTop 1, (Alto.broad.comp hX).eventually_gt_atTop 2000000] with i hv hx he hh
     let R:= hatW (X i); have he': R>0:=lt_trans (by norm_num) hh
     refine ⟨zero_lt_one.trans he,Nat.ceil_pos.mpr he',?_ ,?_⟩; · change 2000000 ≤ Real.log (X i) at hx; linarith only [hx]
     let n':=n i; let m:= radiusB (X i); suffices H:(100000:ℝ)*(m:ℝ)^3 < n'.val from (by exact_mod_cast H)
     have he : (m:ℝ)≤ 2*R:=by have hp : (m:ℝ)< R+1:= Nat.ceil_lt_add_one he'.le; change 2000000 < R at hh; linarith only [hh,hp]
     apply lt_of_lt_of_le _ hv; calc
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) _) he 3) (by positivity : (0:ℝ)≤100000)
        _ < R^4 := by change 2000000<R at hh; nlinarith only [(show 0<R^3 from pow_pos he' 3),mul_pos (show 0<R^3 from pow_pos he' 3) (sub_pos.mpr hh)]
-- n→∞, exp(-a*n/(C B)) sum kill.Volume.Br.L.B^-1. choose int floor n/(100+x) .
noncomputable def lag (n:Side)(x:ℝ) :ℕ:= n.val / (1000*radiusB x)
lemma quell : ∀ᶠ i in φ, let u:=lag (n i) (X i); 10*(u+4)< (n i).val∧10*(u*(4*radiusB (X i)+2)+2*radiusB (X i)) <(n i).val :=by
     filter_upwards [cells hX hn] with i ⟨he,hZ,hY,hm⟩ u; let v:= radiusB (X i); let D:= (n i).val
     have hh:u*(1000*v) ≤ D:= Nat.div_mul_le_self ..
     have hv : v≤v^3:=by apply le_trans (le_of_eq (pow_one v).symm) (pow_le_pow_right₀ hZ (show 1≤ (3:ℕ) by omega)); -- core
     have hp:100000*v<D:= (Nat.mul_le_mul_left _ hv).trans_lt hm; have he: u ≤ u*v:= le_mul_of_one_le_right (Nat.zero_le _) hZ
     change _ < D ∧ 10*(u*(4*v+2)+2*v)< D; constructor<;> nlinarith only [hh,hp,hv,he,hZ] -- omega
lemma cone (a:ℝ) (ha:0<a): Van φ X (fun i=> Midpoint.size (n i)*Real.exp (-a * (lag (n i) (X i)))) ∧ Van φ X (fun i=> Real.exp (-a*lag (n i) (X i))) :=by
     let M(i):= radiusB (X i); let u(i):= lag (n i) (X i); have hm:=cells hX hn; have hx:Run φ X (fun i=> (M i:ℝ)) 0:=Run.Yceil hX (Run.stanza hX) (Eventually.of_forall fun i=>sq_nonneg _)
     have hl:∀ᶠ i in φ,M i*M i ≤ u i:= hm.mono (fun i h=>by
          let v:= M i; have hp:=h.2.2.2; have hv:=h.2.1; apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by norm_num : 0 < (1000:ℕ)) hv)).mpr; change v*v*(1000*v) ≤ _; change 100000*v^3< _ at hp; nlinarith only [hp,pow_pos (show 0<v from hv) 3])
     let q:= -a/2; have hq: q<0:=by unfold q; linarith
     let Ts(i):= Real.exp (q*u i); have hT:Van φ X Ts:=fun b=> ((Van.castE hX hq) b).cash ((hm.and hl).mono fun i h=> by rw [abs_of_pos (by apply Real.exp_pos),abs_of_pos (by apply Real.exp_pos)]; apply Real.exp_monotone; refine mul_le_mul_of_nonpos_left (le_trans (b:=(M i:ℝ)) ?_ (by exact_mod_cast ((le_mul_of_one_le_right (by omega : 0 ≤ M i) (show 1 ≤ M i from h.1.2.1)).trans h.2))) hq.le; exact Nat.le_ceil _)
     have hv : Tendsto (fun i=> (u i:ℝ)) φ atTop:=by
          apply tendsto_atTop_mono' φ ?_ (Alto.broad.comp hX); filter_upwards [hl,hm] with i hi hh; have hg : (M i :ℝ)≤ u i:=by exact_mod_cast (le_trans (le_mul_of_one_le_right (Nat.zero_le _) (show 1 ≤ M i from hh.2.1)) hi)
          exact (Nat.le_ceil (hatW (X i))).trans hg
     let g(i):=((u i:ℝ)+1)^10; have hg:Tendsto (fun i=>Ts i*g i) φ (𝓝 0):=by
          let t(i):= (u i:ℝ)+1; have hb: Tendsto (fun i=> -q*t i) φ atTop:= (show Tendsto t φ atTop from tendsto_atTop_add_const_right φ _ hv).const_mul_atTop (neg_pos.mpr hq)
          have he:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp hb; have hp:0< -q:=neg_pos.mpr hq; have hp':= he.mul_const ((-q)⁻¹^10* Real.exp (-q)); rw [zero_mul] at hp'; refine hp'.congr (fun i=> ?_); change (-q*t i)^10*Real.exp (-(-q*t i))* ((-q)⁻¹^10*Real.exp (-q))= _; have hh:Real.exp (-(-q*t i))*Real.exp (-q)=Ts i:=by unfold Ts; rw [←Real.exp_add]; unfold t; congr 1; ring
          unfold g Ts; unfold Ts at hh; rw [← hh]; unfold t; field_simp; ring; exact mul_inv_cancel₀ hq.ne
     have hn': ∀ᶠ i in φ, (n i).val< (u i+1)*(1000*M i):=(cells hX hn).mono (fun i hi=> by have hp:=Nat.mod_lt (n i).val (show 0 < 1000*M i from Nat.mul_pos (by omega) hi.2.1); have ht : (n i).val % _+(1000*M i)*u i = _:=Nat.mod_add_div ..; rw [add_mul,one_mul,mul_comm (u i)]; omega)
     have hs(i:ι): Real.exp (-a*u i)= Ts i*Ts i:=by unfold Ts; rw [←Real.exp_add]; congr 1; unfold q; ring
     constructor; swap; · simp_rw [show ∀ i:ι,Real.exp (-a*lag (n i) (X i))=Ts i*Ts i from hs]; exact Van.mulL hX (hT 0) hT
     intro b; let B(i) := (1000*(M i:ℝ))^10; have hP := ((hT b).Yrat hX (show Run φ X (fun i=>Ts i*g i*B i) 0 from ((Run.Yplus hX hg).Ymul hX ( (Run.mulK hX hx 1000).Ypow hX 10))))
     apply hP.cash; filter_upwards [hn'] with i hi
     rw [abs_of_nonneg (mul_nonneg (by rw [sizeL];positivity) (Real.exp_pos _).le), hs i, sizeL]; refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hi.le) 10)   (by unfold Ts; positivity)).trans ?_; push_cast; apply le_trans (le_of_eq _) (le_abs_self _); unfold g B;ring
end YM.MSbar.Geneva
