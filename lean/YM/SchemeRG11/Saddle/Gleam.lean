import YM.SchemeRG11.Saddle.Traverse
/-!
# Slicing coordinates, rooted Feynman gauge

For this path RIGHT from TREE first. Never change the zero-mode,
compare on exactly the finite inversion regulator.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice PertExtension.Orb Pert.Orb
variable {G:Gauge}{n:Side}

def branchL (G:Gauge)(hn: Even n.val) : Dir G n→L[ℝ] Potential G n:=
  (twin (G:=G) hn).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ _ _
lemma bark_pos (hn:Even n.val)(A:Dir G n): positiveLinks (branchL G hn A)= representative A:=by
 have he : (branchL G hn A).val=variation A:= twin_twists hn A
 funext l; change G.lieExp ((branchL G hn A).val l)=_
 rw [he]; unfold representative links liftLinks variation genJet splitLink; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; split_ifs <;> simp [Work.F03.exp_neg_color]
lemma energy_at (v:Potential G n): Wilson.energy (positiveLinks v)/2 = wilson v:=by
 unfold Wilson.energy wilson; congr 1; rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun x _=>?_
 let f (u:Axis×Axis):= G.price (plaquette v x u.1 u.2)
 have hh : ∑ p:PlaqAxes, f p.val = ∑ p:Axis×Axis, if p.1<p.2 then f p else 0:=by
   rw [← Finset.sum_filter]; exact (Finset.sum_subtype _ (by simp) _).symm
 symm; rw [Fintype.sum_prod_type] at hh
 refine hh.symm.trans <| Finset.sum_congr rfl fun p _=>?_
 unfold f faceValue; simp [plaquette,travel,square,mul_assoc, add_right_comm x (step p.val.1) (step p.val.2)]
lemma bark_w (hn:Even n.val)(A:Dir G n): wilson (branchL G hn A)=fiscal A:=by rw [← energy_at,bark_pos];rfl

private lemma plog_inv: ∀ᶠ x in 𝓝 (1:G.El), G.plog (G.mat x⁻¹)= -G.plog (G.mat x):=by
 let g(x:G.El):= -G.plog (G.mat x)
 have ht1: ContinuousAt g 1:= (show ContinuousAt (fun x=> G.plog (G.mat x)) 1 from ContinuousAt.comp (x:=1) (f:=G.mat) (g:=G.plog) (by rw [G.mat_one]; exact G.plog_diff.continuousAt) G.continuous_mat.continuousAt).neg
 have ht: Tendsto g (𝓝 1) (𝓝 0):=by simpa [show g 1=0 from by simp [g]] using ht1.tendsto
 filter_upwards [ht.eventually G.plog_left,G.plog_right] with x hx h
 change G.plog (G.mat (G.lieExp (-G.plog (G.mat x))))= _ at hx
 rw [Work.F03.exp_neg_color,h] at hx; exact hx
lemma turned_inv (a:Potential G n)(z:Parameter G n)(l):
    turn a z (Pert.Orb.image l)=(turn a z l)⁻¹:=by
 simp only [turn,positiveLinks]; rw [a.property l]; unfold Pert.Orb.image; dsimp; rw [show -l.1-step l.2+step l.2 = -l.1 by abel,sub_eq_add_neg (-l.1),←neg_add,(show _ ∧ _ from z.property).1 l.1,(show _ ∧ _ from z.property).1 (l.1+step l.2),Work.F03.exp_neg_color]; group
lemma turn_tends(l:Pert.Orb.Links n): Tendsto (fun p:Potential G n×Parameter G n=>turn p.1 p.2 l) (𝓝 0) (𝓝 1):=by
 rw [Push.Loops.tendsto_mat]; exact Eq.subst (motive:=fun x=>Tendsto _ _ (𝓝 (G.mat x))) (turn_zero l) ((turn_smooth _).continuous.continuousAt.tendsto)
lemma rough_actual: ∀ᶠ p:Potential G n × Parameter G n in 𝓝 0, roughLog p.1 p.2∈ LinkP G n:=by
 have he : ∀ᶠ p:Potential G n × Parameter G n in 𝓝 0, ∀ l:Pert.Orb.Links n, roughLog p.1 p.2 (Pert.Orb.image l)= -(roughLog p.1 p.2 l):=by
   refine eventually_all.mpr fun l=>?_ ; simp only [roughLog,turned_inv]; exact (turn_tends l).eventually plog_inv
 exact he
lemma shift_exact: ∀ᶠ p:Potential G n × Parameter G n in 𝓝 0, positiveLinks (shiftedLog p.1 p.2)= turn p.1 p.2:=by
 have he: ∀ᶠ p:Potential G n × Parameter G n in 𝓝 0, ∀ l:Pert.Orb.Links n, G.lieExp (roughLog p.1 p.2 l)=turn p.1 p.2 l:=eventually_all.mpr fun l=>(turn_tends l).eventually G.plog_right
 filter_upwards [rough_actual,he] with p hp he
 let a: Potential G n:=⟨_,hp⟩
 rw [show shiftedLog p.1 p.2=a from balance_same a]
 exact funext he
lemma shift_static: ∀ᶠ v:Potential G n in 𝓝 0, shiftedLog v 0=v:=by
 have he: ∀ᶠ v: Potential G n in 𝓝 0, ∀ l : Pert.Orb.Links n, G.plog (G.mat (G.lieExp (v.val l)))=v.val l:=eventually_all.mpr fun l=> ((takeLink l).toContinuousLinearMap.continuous.continuousAt (x:=(0:Potential G n))).tendsto.eventually G.plog_left
 filter_upwards [he] with v hv
 unfold shiftedLog; rw [show roughLog v 0=v.val from funext fun l=>by simp [roughLog,turn,positiveLinks,hv, -Gauge.mat_lieExp]]; exact balance_same v
lemma shift_zero: shiftedLog (0:Potential G n) 0=0:=mem_of_mem_nhds (s:={v:Potential G n| shiftedLog v 0=v}) shift_static

lemma gauge_solve(hn: Even n.val): ∃ s:Whole G n→ Parameter G n,
    ContDiffAt ℝ ω s 0 ∧ s 0=0 ∧ ∀ᶠ p in 𝓝 0, dLin (shiftedLog (branchL G hn p.1) (s p))= p.2:=by
 let K:=Dir G n × Parameter G n
 let f(x:K): Flow G n:=FPField (branchL G hn x.1) x.2 -- Flow coerces?
 have he: ContDiffAt ℝ ω f 0:=by
    let L: K→L[ℝ] Potential G n × Parameter G n:=((branchL G hn).comp (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
    exact ContDiffAt.comp (g:=fun p:Potential G n × Parameter G n=>FPField p.1 p.2) (f:=L) _ (by rw [map_zero];exact field_smooth) L.contDiff.contDiffAt
 let g(x:K): Whole G n:=(x.1,f x)
 have hg: ContDiffAt ℝ ω g 0:= contDiffAt_fst.prodMk he
 let U := fderiv ℝ g 0
 have hy: U=(ContinuousLinearMap.fst ℝ _ _).prod (fderiv ℝ f 0):=(hasFDerivAt_fst.prodMk (he.differentiableAt (by simp)).hasFDerivAt).fderiv
 let R:= spanLink G n; let H:= (fderiv ℝ f 0).comp (ContinuousLinearMap.inl ℝ _ _)
 have hw1: (fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ _ _)=R.toContinuousLinearMap:=by
   let j:= ContinuousLinearMap.inr ℝ (Dir G n) (Parameter G n)
   have hs: f ∘ j= FPField 0:=by
      funext t; change FPField (branchL G hn 0) t = _;rw [map_zero]
   have ht : fderiv ℝ f 0 ∘L j = fderiv ℝ (f ∘ j) 0:=by
      rw [fderiv_comp 0 (by rw [map_zero]; exact he.differentiableAt (by simp)) j.differentiableAt,map_zero, ContinuousLinearMap.fderiv]


   rw [ht,hs]; exact FPDeriv_flat
 have hw(a:Dir G n)(z:Parameter G n): U (a,z)=(a,H a+R z):=by
   rw [hy]; change (a,fderiv ℝ f 0 (a,z))=_
   rw [show (a,z)=(a,(0:Parameter G n))+(0,z) by simp,map_add]
   exact congrArg (fun t=>(a,H a+t)) (DFunLike.congr_fun hw1 z)
 let e : K≃L[ℝ]Whole G n:=
   { U with
     toFun:=U
     invFun:= fun x=> (x.1,R.symm (x.2-H x.1))
     left_inv:=fun x=>by rcases x with ⟨a,z⟩; change ((U (a,z)).1,_)=(a,z); rw [hw]; simp
     right_inv:=fun x=>by rcases x with ⟨a,t⟩; change U (a,R.symm (t-H a))=(a,t); rw [hw]; simp
     continuous_invFun:=by
       apply Continuous.prodMk continuous_fst; exact R.symm.continuous.comp (continuous_snd.sub (H.continuous.comp continuous_fst)) }
 have hJ : HasFDerivAt g (e:K→L[ℝ]Whole G n) 0:=(hg.differentiableAt (by simp)).hasFDerivAt
 have hk : ω≠(0:WithTop ℕ∞):=by simp
 let j := hg.localInverse hJ hk
 have hud: g 0 = 0:=by
    refine Prod.ext rfl ?_; change dLin (shiftedLog (branchL G hn 0) 0)=0; rw [map_zero,shift_zero,map_zero]
 have hu : ContDiffAt ℝ ω j 0:= hud ▸ hg.to_localInverse (f':=e) hJ hk
 have hz : j (g 0)=0:=mem_of_mem_nhds (s:={v|j (g v)=v}) (hg.hasStrictFDerivAt' hJ hk).eventually_left_inverse
 rw [hud] at hz
 refine ⟨fun p=>(j p).2, hu.snd,?_,?_⟩
 · exact congrArg Prod.snd hz
 have hi1: ∀ᶠ x in 𝓝 (g 0), g (j x)=x:=(hg.hasStrictFDerivAt' hJ hk).eventually_right_inverse
 have hi: ∀ᶠ x in 𝓝 0, g (j x)=x:=by rwa [hud] at hi1
 filter_upwards [hi] with x hx
 rw [←show (j x).1=x.1 from congrArg Prod.fst hx]; exact congrArg Prod.snd hx

def swing (G:Gauge)(hn:Even n.val): Whole G n→ Parameter G n:= Classical.choose (gauge_solve hn)
lemma swing_smooth (G:Gauge)(hn:Even n.val): ContDiffAt ℝ ω (swing G hn) 0:=(Classical.choose_spec (gauge_solve hn)).1
lemma swing_flat (G:Gauge)(hn:Even n.val): swing G hn 0=0:= (Classical.choose_spec (gauge_solve hn)).2.1

def graze(hn:Even n.val)(p: Whole G n): Potential G n:= shiftedLog (branchL G hn p.1) (swing G hn p)
lemma graze_smooth(G:Gauge)(hn:Even n.val): ContDiffAt ℝ ω (graze (G:=G) hn) 0 :=by
 let f(p:Whole G n):= (branchL G hn p.1,swing G hn p)
 have he : f 0=(0,0):=by simp [f,swing_flat]
 exact (he.symm ▸ (shift_smooth (G:=G) (n:=n)) : ContDiffAt ℝ ω (fun p:Potential G n× Parameter G n=> shiftedLog p.1 p.2) (f 0)).comp 0 (((branchL G hn).contDiff.contDiffAt.comp (0:Whole G n) contDiffAt_fst).prodMk (swing_smooth G hn))
lemma graze_flat(G:Gauge)(hn:Even n.val): graze (G:=G) hn 0=0:=by simp [graze,swing_flat,shift_zero]
lemma graze_div (G:Gauge)(hn:Even n.val): ∀ᶠ x:Whole G n in 𝓝 0, dLin (graze hn x) = x.2:= (Classical.choose_spec (gauge_solve hn)).2.2
lemma graze_eq(G:Gauge)(hn:Even n.val): ∀ᶠ x:Whole G n in 𝓝 0, positiveLinks (graze hn x)= Lattice.gauge (fun l=> G.lieExp ((swing G hn x).val l)) (representative x.1):=by
 let f(p:Whole G n):=(branchL G hn p.1,swing G hn p)
 have h: f 0=0 :=by simp [f,swing_flat]
 have hc : Tendsto f (𝓝 0) (𝓝 0):=h ▸ (((branchL G hn).continuous.continuousAt.comp continuousAt_fst).prodMk (swing_smooth G hn).continuousAt).tendsto
 filter_upwards [hc.eventually shift_exact] with x hx
 unfold graze; rw [show positiveLinks (shiftedLog (branchL G hn x.1) (swing G hn x))= turn (branchL G hn x.1) (swing G hn x) from hx]; funext; simp [turn,bark_pos,Lattice.gauge]

end YM.SchemeRG11.Sway
