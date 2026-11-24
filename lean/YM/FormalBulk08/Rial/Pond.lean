import YM.FormalBulk08.Rial.Pep

/-! Stencil reproof log→letter. No analyticity on infinite cover. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {S:Finset Cover} {d:ℕ} {F: Frame G d} {I:Type*} {j u l r D:ℕ} {η A : ℝ}

def funnels (S:Finset Cover)(X: Snap G d): Jets.Rays (SpotC S G):=(sofas G S).symm (Film.localLane X)
lemma funnels_diff : ContDiffAt ℝ ω (funnels S (G:=G) (d:=d)) 0:= (sofas G S).symm.contDiff.contDiffAt.comp _ (Film.local_smooth ..)
lemma funnels_zero : funnels S (0:Snap G d)=0:= by rw [funnels, Film.local_zero S,map_zero]
lemma funnel_read (x : Snap G d)(v:SpotC S G): funnels S x v= Pose.curtain (chamber S G v) x := by
   change Film.lane (Place.seat _) (Place.beam v.1) x v.2=_; unfold Pose.curtain; rw [show bearing (chamber S G v)= Place.beam v.1 from axisEquiv.symm_apply_apply _]; rfl

variable (T:SectionData F)(i: F.Index)
def hive (x:Letter F):Snap G d→ℝ:= lights T (mint F x) ∘ funnels T.stencil
lemma grounds (j) (v:Snap G d): Tensor.diagonal (Tensor.coeff (lights T i) j 0) (funnels T.stencil v) =
    ∑ t: chain (SpotC T.stencil G) j, rancho (paste (lights T i)) j j t * tier (chamber _ _ ∘ t) v:= by
    rw [show Tensor.diagonal (Tensor.coeff (lights T i) j 0) (funnels T.stencil v)=_ from (show traceP (funnels T.stencil v) (coeff j (paste (lights T i)))=_ from trace_paste ..).symm]
    unfold rancho; let P:= paste (lights T i); let z:= marble j (coeff j (paste (lights T i))); let p:= (funnels T.stencil v : Jets.Rays (SpotC T.stencil G)); have h : coeff j P=facade j z := by rw [show facade j z=_ from marble_grade .., MvPolynomial.homogeneousComponent_eq_self (paste_grade ..)]
    change traceP p (coeff j P)= ∑ t: chain (SpotC T.stencil G) j, z t*_
    rw [h]; unfold traceP; simp only [facade_eq,map_sum,map_mul,MvPolynomial.aeval_C];apply Finset.sum_congr rfl; intro w _; simp only [Pose.tier,cards,map_prod,MvPolynomial.aeval_X]; apply congr_arg; exact Finset.prod_congr rfl (fun i _=> funnel_read ..)
lemma anthem_slate (a : Loc G 1) (M:Tile (SpotC S G) r) (k n:ℕ) (x: Fin n→Snap G k) : slate (hymn M) k n x=∑ v:chain (SpotC S G) r, M v * Tensor.coeff (tier (chamber _ _ ∘ v)) n 0 x:= by
    obtain ⟨C,hC⟩:= hymn_bill M 1 (0,a); rw [slate_read a _ x one_pos hC]; let f(t:chain (SpotC S G) r):=chamber S G ∘ t
    have hf: Injective f:= fun u v h=>funext fun i=>chamber_safe _ _ (congr_fun h i)
    let g (v:chain (edgeL G) r):= hymn M v * Tensor.coeff (tier v) n 0 x
    change (∑' v,g v)= _; rw [←hf.tsum_eq (f:=g) ?_,tsum_fintype]; swap;· intro u hu; change g u ≠0 at hu; by_contra H; apply hu; unfold g; rw [hymn_floor M u (fun i h=>H ⟨i,h⟩),zero_mul]
    apply Finset.sum_congr rfl; intro u _;unfold g f; rw [hymn_power]
lemma real_soaps (H:Hol G)(hs:T.Sound H)(p: Dev T.stencil G): (↑(column T i p).re:ℂ)=column T i p:= by
    apply Complex.conj_eq_iff_re.mp
    have h:=hs.ordinary_real (copy F i) (pore p)
    rw [show star (copy F i)=copy F i from ?_] at h; swap; · unfold copy; funext k; by_cases h:i=k<;> simp [h]
    exact h.symm
lemma lysine (H : Hol G)(hs:T.Sound H)(x:Letter F): Complex.ofRealCLM ∘ hive T x = slant T (copy F (mint F x)) ∘ Film.localLane := by funext v;change (↑(hive T x v):ℂ)=_; unfold hive; simp only [Function.comp_apply,funnels,lights,ContinuousLinearEquiv.apply_symm_apply]; exact real_soaps T _ H hs _
end YM.FormalBulk08.Rial
