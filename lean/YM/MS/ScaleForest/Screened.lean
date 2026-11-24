import YM.MS.ScaleForest.PageOne
/-!
# If the marginal jet in a *new* parent of some already
calculated UV subgraphs vanishes, so does that parent's pole

A sufficiency test used on the ARM of the ghost example. The hypotheses use
Taylor test on **each** explicit page (so hold dimension and any negative
local parts included in the children). Accordingly this particular (Jet0)
test doesn't serve cases where holomorphy holds only by cancellations
between different pages.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {b:Bool} {r:ℤ} {m n j h ℓ : ℕ} {u z : ℂ} {X : Mob G} {V : Flats G}

private theorem passLow (hp:kPrice X) {w : Legs (Shore G m)} (hv:mass w+n=h) (hu:j>h) (ha:0 < u.re+j) :
    Tad (progress j u X) h m w=0:= by
    let f(t:ℝ):= wood j u t X
    let F(t:ℝ):= fieldVal (f t m) (ray w)
    have ht : Majorant μ0 F := matt_w (u:=fun _:Unit=>u) (f:=fun _=>X) (k:=j) (a:=u.re+j) hp (fun i=>le_rfl) ha () (ray w)
    let A(t:ℝ):= (Nat.factorial n:ℝ)⁻¹ • iteratedDeriv n (F t) 0
    have hs(t:ℝ):Tad (f t) h =0:= by unfold f; rw [wood,Tad_scale (clear_p hp _),flat hp hu,smul_zero]
    have he(t:ℝ):A t= Tad (f t) h m w:= by rw [t_bud _ hv,torch_at]; rfl
    rw [t_bud _ hv,torch_at]; unfold reading; change ((Nat.factorial n: ℝ)⁻¹) • iteratedDeriv n (fun p=>∫ t, F t p ∂μ0) 0=_
    unfold iteratedDeriv; rw [ht.identity, ContinuousMultilinearMap.integral_apply (ht.integ n 0), ← integral_smul]; change (∫ t, A t ∂μ0)=_; simp_rw [he,hs]; simp

def Jet0 (h:ℕ)(X:Flats G): Prop :=∀ n:ℕ, ∀ᶠ z in dotty,Tad (X n z) h=0
lemma kprice_sum_term {I : Type}(l:Finset I)(F:I→Mob G)(hp:∀ i∈l,kPrice (F i)): kPrice (∑ i∈l,F i):= fall_sum l (f:=fun i (_:Unit)=> F i) hp (fun _=>zero_le_one)

lemma progressJet (hp:kPrice X) (hu:j>h) (ha:0<u.re+j) : Tad (progress j u X) h=0:= by
   funext m w
   by_cases ht:(h:ℤ) < mass w; exact t_exc ht
   exact passLow hp (n:=((h:ℤ)- mass w).toNat) (by omega) hu ha

lemma blessJet (hp:kPrice X)(ha:0<(vamp z h ℓ).re+↑(h+1:ℕ))(hv:Tad X h=0): Tad (Bless h ℓ z X) h=0:= by
   unfold Bless; split; simp only [add_zero, progressJet hp (Nat.lt_succ_self h) ha]
   let u:= vamp z h ℓ; let n:ℕ:=h+1
   have ht(i:ℕ) (c:ℂ): kPrice (c • Tad X i):= by convert! fall_scale (U:=fun _:Unit=>c) (tad_price hp i) (const_sc ..) using 1; ext; simp
   have he: kPrice (cPos n u X):= kprice_sum_term _ _ (fun i _=>ht i _)
   rw [t_plus (prog_mint hp ha) he, progressJet hp (Nat.lt_succ_self h) ha]; unfold cPos; rw [zero_add, sumT];
   · refine Finset.sum_eq_zero fun i _=>?_; rw [t_pose,t_already i hp]; split; · next he=> subst i; rw [hv,smul_zero];
     exact smul_zero _
   exact fun i _=> ht i _

lemma integrateJet (hJ : Sewable b r h 0 V) (hV : Jet0 h V) : Jet0 h (integratePages h V) := by
   intro i; have hp: mer (V i):=(clockMoon hJ.clock i).mer
   rw [integrate_each]; filter_upwards [hp.price, vamp_up h i, hV i, uv_limit (ell:=i) (h:=h) hp (fun hh=> by rw [hh]; exact hJ.start)] with z hP he hr hv
   rw [hv.1]; exact blessJet hP he hr

private lemma parade_initial (R:Flats G): Parade R h 0 0 z= ∑ i∈R.support,R i z:= by simp only [Parade,Finsupp.sum,hikeP, Pearl.weight,amount,Complex.ofReal_zero,zero_mul, Complex.exp_zero, posing, one_smul]

lemma detects (ht : Sewable b r h 0 V) (hV : Jet0 h V) (hs : Stay h V) : counterterm (integratePages h V)=0 := by
    let X:= integratePages h V; let P:= counterterm X; let f:= Parade X h 0 0
    obtain ⟨hv,hP⟩:= integrate_sewable ht; obtain H:= pole_cancels hP hv hs
    have he : Parade (X + collapsed P) h 0 0 = f + P := by rw [ page_add,pureP P H.count]
    have hy: Jet0 h X:= integrateJet ht hV
    have hw: Moony b X:= clockMoon hP.clock
    obtain ⟨F,hF⟩: Live (f+P):= he ▸ H.stay 0 0
    have hx : ∀ᶠ z in dotty,Tad ((f+P) z) h=P z:= by
        filter_upwards [ (eventually_all_finset X.support).mpr (fun i _=> (hy i).and (hw i).mer.price),
           (ct_kernel hP).fine.tune.mer.price ] with z hJ hZ
        let A i:= X i z;
        have hR:kPrice (f z):= by unfold f; rw [parade_initial]; exact kprice_sum_term _ _ fun i hi=> (hJ i hi).2
        have hh :Tad (f z) h=0:= by unfold f; rw [parade_initial,sumT]; exact Finset.sum_eq_zero (fun i hi=> (hJ i hi).1); exact fun i hi=> (hJ i hi).2
        rw [Pi.add_apply,t_plus hR hZ, hh,zero_add]; exact (H.eq_tad z).symm
    exact deep_zero (ct_cool _) (Lift.wind (Lift.congr (Taylor_lift hF h) hx))

lemma on_branch {X:GraphSum G true 4}{Y:GraphSum G b h}{U:LineRule G} (hp: Jet0 h (connect b U X.instructions.renorm Y.instructions.renorm)) : (bridge U X Y).instructions.pole=0:= by
    obtain ⟨he,hr,hf⟩:= (bridge U X Y).accepted.force; exact detects ⟨he,hf⟩ hp hr
end YM.MS.ScaleForest
