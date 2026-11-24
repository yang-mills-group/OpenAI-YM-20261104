import YM.Progress.JOINT_CALENDAR.Germs
import YM.PCalc.Band
import YM.RG02.Limit.Radial

/-!
Recover the orientation Ward property of THIS possible `Kin` supply,
without calling another constructor (other periods would matter!). Thus the
`metric` in its bed really does give the same-Haar-chart log Hessian as the
F03/A/Fk prescription, on the period being used. Need no stronger schedule
stencil margin beyond the actual calibration; finite-period calculation.
No uniqueness of infinite-cover truncation choices follows here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Orientation
open Filter Function Matrix Lattice Wilson RG Precision Exterior Tree Supply Bid
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n c f : Side}{S : StepData c f}

lemma swap (W : PathData G)(D : Bed){p σ s A b Y}(h : W.Bounds p σ s A)(he : Attached D W)
    (hf : Floor D p n b Y)(x y : Dir G n) : gaugeFiscal D x y=gaugeFiscal D y x := by
   rw [Work.F03.metric_pair D h he _ _ hf, Work.F03.metric_pair D h he _ _ hf];
   simp_rw [real_inner_comm (Work.F03.faceCurl _ x), real_inner_comm (Work.F03.ellLine W _ x)]

private lemma origin_symmetric {D : Bed} (F : Dir G n→ℝ)(H : ContDiffAt ℝ ω F 0)
    (he : ∀ x y, iteratedFDeriv ℝ 2 F 0 ![x,y]=gaugeFiscal D x y)
    (hf : ∀ (s : Signed) (x : Dir G n)(a : ℝ), F (a • pulled x s)=F (a • x)) : Sworn D n G := by
   intro s x y
   open PertExtension.Series.Radial in
   have hh (x : Dir G n) : iteratedFDeriv ℝ 2 F 0 ![pulled x s,pulled x s] = iteratedFDeriv ℝ 2 F 0 ![x,x] := by
      have hx : Asym.layer F (pulled x s) = Asym.layer F x := Asym.Near.unique' (by
         convert (Asym.layer_ray (H.of_le le_top) (pulled x s)) using 1
         funext t; rw [hf]) (Asym.layer_ray (H.of_le le_top) x)
      · have hu := congr_arg (fun z => PowerSeries.coeff 2 z) hx
        simp only [Asym.layer,PowerSeries.coeff_mk] at hu
        have heq := Complex.ofReal_injective hu
        simp only [jet] at heq
        have hg (a : Dir G n) : ![a,a]=(fun _=>a) := by funext i; fin_cases i <;> rfl
        rw [hg,hg]; exact mul_left_cancel₀ (by norm_num) heq
   have hu z : (Work.F05.bend F 0) (pulled z s) (pulled z s) = (Work.F05.bend F 0) z z := by rw [Work.F05.bend_apply, Work.F05.bend_apply, hh]
   have hy (a b : Dir G n) : Work.F05.bend F 0 a b=Work.F05.bend F 0 b a := by
      simp only [Work.F05.bend_apply,iteratedFDeriv_two_apply]; exact H.isSymmSndFDerivAt_of_omega ..
   have hv : pulled (x+y) s = pulled x s+pulled y s := by
      funext i; unfold pulled; simp only [Pi.add_apply]; split <;> simp; abel
   have hs:= hu (x+y)
   simp only [hv,map_add,LinearMap.add_apply] at hs
   rw [hu,hu,hy y x, hy (pulled y s) (pulled x s)] at hs
   simp_rw [Work.F05.bend_apply,he] at hs
   linarith

lemma top_oath {p:Clip}{D:Bed}{W:PathData G}{σ w A u v}(ht : W.Bounds p σ w A)
    (ha : Attached D W)(H : Floor D p n u v)(hh : D.diagonal.acts n=1) : Sworn D n G := by
   open Progress.Joint Work in
   refine origin_symmetric _ energy_born (F03.hessian_of_limit ((energy_born (G:=G) (n:=n)).of_le le_top)
     (fun z => energy_limit D z H hh) F03.gaugeFiscal_add (swap W D ht ha H)|>.2.2) ?_
   intro s x a; rw [← Work.F03.represent_pulled,Wilson.energy_pull]

/-- The actual Hessian matching port, here recover from receipts even
if no exploration of another period. `F03.answer` on weaker size input
by its from_flat identities. -/
lemma recovers (B : Bed){p : Clip}{W : PathData G}{u v σ C Λ}(T : Forest S.ratio)
    (h : S.patch.Branches S.kernel G)(hb : W.Bounds p σ C Λ)(ht : Attached B W) (hf : Floor B p f u v) (hs : Sworn B f G) : Comptroller T B p W := by
   intro k F
   open Work F03 in
   have hg : ContDiffAt ℝ ω (F03.flat S k p W) 0 := F03.flat_smooth h k (F02.answer G p W _ _ _ hb)
   obtain ⟨hx,hy,hz⟩ := Work.F03.flat_jets h k hb ht hf hs (Work.F02.answer G p W _ _ _ hb)
   have hv : F =ᶠ[𝓝 0] Work.F03.flat S k p W ∘ Work.F03.inclusion T := Work.F03.from_flat T k W p
   have hp:= Work.F03.hessian_comp (Work.F03.inclusion_zero T) (hg.of_le le_top)
       ((Work.F03.inclusion_smooth T).of_le le_top) hy
   refine ⟨hv.eq_of_nhds.trans (by simp only [Function.comp_apply, Work.F03.inclusion_zero,hx]), hv.fderiv_eq.trans hp.1,fun a b =>?_⟩
   simp_rw [(hv.iteratedFDeriv ℝ 2).self_of_nhds, hp.2,hz,Work.F03.inclusion_deriv]; rfl

lemma channels_swap {p : Clip}{W : PathData G}(s : Signed)(U : Config G n) : mainTerm p W (pull s 0 U)= mainTerm p W U := by
    let F q := quadratic p W (pull q 0 U)+uncut W.cubic (pull q 0 U) + uncut W.quartic (pull q 0 U)
    unfold mainTerm
    simp_rw [pull_pull, affine,Signed.act_zero,add_zero]
    unfold Patch.average; apply congr_arg (fun t => (Fintype.card Signed:ℝ)⁻¹ * t)
    exact Equiv.sum_comp (Equiv.mulLeft s) F

lemma oath {O : ChartRatio G} {K : MapPrices}{a : Levels G}{M : Horizon a}{p : Supply.Sheet G}{q : Supply.Rolls p}{Q : Precision.PostCost q}
    {R : Kin M O} (hk : M.Suffices K)(hr : R.Planned Q) {N m : ℕ}(hp : m≤N)(P : ℕ) : Sworn (M.H N m) (a.S.side m P) G := by
   induction hp using Nat.decreasingInduction with
   | self => exact top_oath (hr.cap N N le_rfl) (hr.links N N le_rfl) (hk.all N N le_rfl _) (hk.top N _)
   | of_succ m hm ih =>
      obtain ⟨v : Forest (a.clock.op m P).ratio⟩:= Tree.select (a.clock.op m P).ratio (a.clock.op m P).patch.odd_side
      let t : (a.clock.op m P).Choices := Classical.arbitrary _
      obtain ⟨hc,hg⟩ := hr.critical N m P hm v
      have h := Work.F04.stationary_value v _ _ (M.H N (m+1)) (M.H N m) _
          (hk.crossings N m P hm).trial (recovers _ v (a.blocks .. |>.branches) (hr.cap N (m+1) hm) (hr.links N (m+1) hm) (hk.all N (m+1) hm _) ih) _ hc (fun x =>
            (Push.side (R.stationary N m P v) (hc.2.1.differentiableAt (by simp)) x).unique (hg x)) t
      have hl := hr.classicalPart N m P hm v 2 (by omega) t
      let V := R.path N m
      let T := fun x : Dir G (a.S.side m P)=> mainTerm (a.params m).clip V (represent x)
      have he a' b' : iteratedFDeriv ℝ 2 T 0 ![a',b']=gaugeFiscal (M.H N m) a' b' := by
         have hi := Work.F03.hessian_of_limit (h.2.1.of_le le_top) (Progress.Joint.fiscal_limit (M.H N m)) Work.F03.gaugeFiscal_add
             (swap (R.path N m) _ (hr.cap _ _ hm.le) (hr.links _ _ hm.le) (hk.all _ _ hm.le _))
         unfold T V; rw [← hl.2.2,h.2.2]; exact hi.2.2 a' b'
      refine origin_symmetric T hl.2.1 he ?_
      intro s x e; unfold T; rw [← Work.F03.represent_pulled, channels_swap]

lemma certifies {O : ChartRatio G}{S : Supply.Sheet G}{q : Supply.Rolls S}{a : Levels G}{K : MapPrices}{Q : Precision.PostCost q}
    {M : Horizon a}{R : Kin M O}(hk : M.Suffices K)(hr : R.Planned Q){N m : ℕ}(P : ℕ)(h : m<N)(F : Forest (a.clock.op m P).ratio) :
    Comptroller F (M.H N (m+1)) (a.params (m+1)).clip (R.path N (m+1)) :=
    recovers _ F (a.blocks m P).branches (hr.cap N (m+1) h) (hr.links N (m+1) h) (hk.all N (m+1) h _) (oath hk hr h P)
end YM.RG02.Orientation
