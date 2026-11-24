import YM.OPE.Compatible.Bowman.Forth
/-!
# Universal nonzero quadratic moment (real axis scribe). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n c:Side}{S:StepData c c}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r m:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
abbrev roseM (a:Axis)(c:Cover):ℝ:= (c a:ℝ)^2
def swale (a b:Axis) :fieldX (TypeFace 1):= fun i=> if i.2=coord b then roseM a i.1 else 0
lemma wild (a b:Axis) : Quiet (swale a b) 2:=by
    refine ⟨1,zero_le_one,fun i=>?_⟩; unfold swale; rw [one_mul]; split
    · unfold roseM; rw [norm_pow,Real.norm_eq_abs,show |((i.1 a:ℤ):ℝ)|=(↑((i.1 a).natAbs):ℝ) from by simp]; apply pow_le_pow_left₀ (Nat.cast_nonneg _); exact_mod_cast ((Finset.single_le_sum (f:=fun j=> (i.1 j).natAbs) (fun i _=>Nat.zero_le _) (mem_univ a)).trans (Nat.le_add_left (size i.1) 1))
    rw [norm_zero]; exact zero_le_one.trans (poise_one ..)
lemma berry (a k:Axis)(z):
    movesX ℝ k (roseM a) z= if k=a then 2*(z a:ℝ)+1 else 0:=by
       by_cases H:k=a; subst k; simp [moveX_eq,roseM];ring
       rw [moveX_eq,if_neg H]; simp [roseM, Ne.symm H]
lemma bogie (a b:Axis)(h:a<b)(z:Cover)(p:PlaqAxes) : meetsX (cobound 1) (swale a b) (z,plaquette p)= if p.val=(a,b) then 2*(z a:ℝ)+1 else 0:=by
    let i:= p.val.1; let j:=p.val.2; have hp :i<j:=p.property
    have he(u:Axis): sea (coord u) (swale a b)= if u=b then roseM a else 0:=by ext v; unfold sea swale; by_cases H:u=b<;>simp [H,coord_iff]
    rw [coarea (wild ..),he,he]; by_cases hk:i=a∧ j=b
    · have hh :p.val=(a,b):=Prod.ext hk.1 hk.2; simp only [hh,if_true,if_neg h.ne,map_zero, Pi.zero_apply,sub_zero]; rw [berry]; simp
    rw [if_neg (show p.val≠ _ from fun he=> hk (⟨congr_arg Prod.fst he,congr_arg Prod.snd he⟩))]; change movesX ℝ i (if j=b then roseM a else 0) z-movesX ℝ j (if i=b then roseM a else 0) z= _
    by_cases hx:j=b
    · rw [if_pos hx, if_neg (hx ▸ hp.ne), berry,if_neg (fun h=> hk ⟨h,hx⟩), map_zero]; simp
    rw [if_neg hx,map_zero,Pi.zero_apply]; split
    next hz=> rw [berry, if_neg (show j≠a from (lt_trans h (hz ▸ hp : b<j)).ne')]; simp
    next hz=> simp
lemma dew (h:4≤ i)(K:KernelChoices)(v:Train i) : (pink K.penalty v).read 0 = 1:=by
     have hP : (0:Momentum)∈ baseCube:=⟨by unfold Next.Free.physical; simp,by intro i; simp [Real.pi_pos.le]⟩
     rw [show (pink _ v).read _=_ from (heart_true K.penalty K.penalty_pos h v).1.echo 0 hP,pulse, Train.bend_zero, inv_one,one_smul]; simp only [Train.bulb_zero,inv_one]; exact mask_one ..
lemma anthem (a b: Axis)(h:a<b)(H: FreeResolvent.FaceRow)(he: H.read 0=1)(hp:Whole H)(x:Cover): meetsX (barrage H) (swale a b) (x,coord b)= -2:=by
    let p:PlaqAxes:=⟨(a,b),h⟩; let Y:= swale a b; let T:= meetsX (cobound 1) Y; have hg(k:Axis)(j:TypeFace 2)(x:Cover):swipe k T (x,j)= if k=a∧ j=plaquette p then (2:ℝ) else 0:=by
       obtain ⟨i,rfl⟩:=plaqEquiv.surjective j; change meetsX (cobound 1) (swale a b) (x+step k,plaquette i)-meetsX _ _ (x,plaquette i)= _; rw [bogie a b h, bogie a b h]; by_cases ht:i=p
       · subst i; by_cases hh:k=a; subst k; simp [p, ← plaq_map]; ring
         simp [p,hh,Ne.symm hh]
       have hx:i.val ≠ (a,b):= fun e=> ht (Subtype.ext e); rw [if_neg hx, if_neg hx, if_neg]; simp
       exact fun h=> ht (plaqEquiv.injective h.2)
    have hb(k:Axis): meetsX H (swipe k T) = fun x:Cover × TypeFace 2=>if k=a∧ x.2=plaquette p then 2 else 0:=by rw [show swipe k T = _ from funext fun i=>hg k i.2 i.1]; exact axis_mem H hp he (fun j=> if k=a∧j=plaquette p then 2 else 0)
    have hu := peck hp (d':=0) 0 (wild a b) x b
    change meetsX (barrage H) Y _ = _ at hu; rw [hu]; change -(∑ k:Axis,∑ j:TypeFace 2,left ℝ 1 k j (coord b)*meetsX H (swipe k T) (x-step k,j)) = _; simp_rw [hb]; rw [sum_eq_single a, sum_eq_single (plaquette p)]; rw [if_pos ⟨rfl,rfl⟩,Script.plank,if_pos ⟨rfl,rfl⟩,one_mul]
    · intro i _ hi; simp [hi]
    · simp
    · intro i _ hi; simp [hi]
    simp
lemma fundamental (a b:Axis)(h:a<b)(K:KernelChoices)(v:Train i)(hn:4 ≤ i): ∑' x:Cover,(Op K v) (coord b) (coord b) x*roseM a x= -2:=by
    let P:= Op K v; let H:=pink K.penalty v; let Y:= swale a b; have hp :Whole P:= Op_whole hn v; have ht:=meets_current hp (wild a b) 0 (coord b); let F(x:Cover)(t:TypeFace 1):= P (coord b) t x * Y (0+x,t); have hu :Summable (uncurry F):=ht
    have hx : meetsX P Y (0,coord b)=(∑' x:Cover,(Op K v) (coord b) (coord b) x*roseM a x):=by unfold meetsX; change (∑' i,uncurry F i)=_; rw [hu.tsum_prod]; apply tsum_congr; intro i; rw [tsum_eq_single (coord b)]; unfold F Y swale; simp [P]; intro t ht; unfold F Y swale;simp [ht]
    have hv:= (heart_heats K.penalty K.penalty_pos hn (fun i:Train i=> i)).1.stock.whole v
    rw [← hx,show P=barrage H from bank_injective hp.safe (barrageH hv).safe fun n=> by rw [barrage,(Whole.boundary _|>.flipped).acts (hv.prod (Whole.boundary _)), hv.acts (Whole.boundary _),acts_trans]; unfold P; rw [Op_stays hn];exact Matrix.mul_assoc ..]
    exact anthem a b h H (dew hn ..) hv _
end Script
end YM.OPE.Flume
