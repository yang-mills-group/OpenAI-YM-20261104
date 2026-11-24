import YM.WilsonCoeffUV.Vacuum.UV.Moment
/-!
# Low order check

Explicit first kinetic correction from vertices by twice heat and connected bracket.
Full Wick, no ghost/truncated covariance substitution. This is a coefficient
formula (not comparison to calibration or an MS beta coefficient).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{Ñ:ChartRatio G}{A:Levels G}

namespace Bloom
variable (A:Levels G)(Ñ:ChartRatio G) (N m:ℕ)
abbrev lign:= stellar (loose A m) A.clock.kernel Ñ (middleF A m N) (actionW A Ñ N (m+1))
abbrev truss : ropes Cover (Hinge G (loose A m).L) (Hinge G (loose A m).L):= stair (upper (leftF A m N) 0) 0
abbrev peat:= spurs (loose A m) A.clock.kernel Ñ (leftF A m N) (middleF A m N) (actionW A Ñ N (m+1))
abbrev amberK:= snow (loose A m) A.clock.kernel Ñ (leftF A m N) (middleF A m N) (actionW A Ñ N (m+1))
variable {A Ñ N m}
lemma hours (g:G.Simple)(h: LocalRatio Ñ)(p:m<N)(b:3*e <r+2*k): peat A Ñ N m k e r=0:=by
    let P:=loose A m; let K:=A.clock.kernel; let Z:= freeForms A N (m+1);
    let Q:= (story A Ñ N (m+1)).1
    have hp:= old A Ñ g h N _ p
    have he:= spurs_enter P K Ñ Z Q (roam A N m) (A.blocks m 0).branches h hp.patch (resin A N m p) k e r
    apply he.unique; apply Yields.zero.congr; apply Eventually.of_forall; intro n
    let S:= mStep A n m; let R:= xree P K n; let V:= xray S R Z (roam A N m n) Ñ (Q (n*P.L))
    have hh: V k e r=0:= by apply span_abr _ (pack_band (M:=extractV G S R (roam A N m n)) S (hp.basis _).lamp) (pack_zero S h); exact Or.inr b
    change 0 = turnTen (weaveH (ratioN P.L n) G) (V k e r)
    rw [hh]; rfl

lemma early_sum (k r x)(g:G.Simple)(h:LocalRatio Ñ)(p:m<N)(hv:x≤3+3*k)(hg:3*k<r+2*x): amberK A Ñ N m k r=scoop (∑ j∈ Finset.range x, peat A Ñ N m j k r):=by
   unfold amberK snow sluice; rw [Finset.sum_apply]; congr 1; symm
   refine Finset.sum_subset (Finset.range_mono hv) (fun i ht hh=>?_); apply hours g h p; have hh : x ≤ i:= by simpa using hh
   omega
-- cubic via classical leaves; Haar germ still present in definition but no valence here
lemma virgo (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): amberK A Ñ N m 1 3=scoop (lign A Ñ N m 1 3):= by
   rw [early_sum 1 3 1 g h p (by omega) (by omega)]; simp only [Finset.sum_range_one,peat,spurs,tide_zero]
-- ray cross at order k=1: Curl sums vanish.
section
variable {X:Type}
variable {S:ropes Cover X X}{Y:Layers ℝ (Cloth X)}
-- use ℝ only; expand z diagonal
lemma vanish_cross (h:∀ i, Y i 0=0)(r): curlJ S Y Y r 1=0:= by
   unfold curlJ; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j hj; apply trim_zero (α:=X)
   have hf:= Finset.mem_antidiagonal.mp hj; by_cases hr:j.2=0; · rw [hr]; exact Or.inr (h _)
   rw [show j.1=0 by omega]; exact Or.inl (h _)
lemma once_cross (h:∀ i,Y i 0=0)(r): curlJ S Y Y r 2= ∑ j∈ Finset.antidiagonal r, whittle S (Y j.1 1) (Y j.2 1):=by
   unfold curlJ; apply Finset.sum_congr rfl; intro j hj; rw [Finset.sum_eq_single_of_mem (1,1)]
   · exact Finset.mem_antidiagonal.mpr rfl
   intro i hi hb
   apply trim_zero
   have hf:= Finset.mem_antidiagonal.mp hi; by_cases hr:i.2=0; · rw [hr]; exact Or.inr (h _)
   have he : i.1=0:=by by_contra h; exact hb (Prod.ext (show i.1=1 by omega) (show i.2=1 by omega))
   rw [he]; exact Or.inl (h _)
end
variable (A Ñ N m)
-- connected operations and Jacobian joint vertices BOTH included
def glow : Gen ℝ (Cloth (Hinge G (loose A m).L)) := crimp (truss A N m) (lign A Ñ N m 2)+whittle (truss A N m) (lign A Ñ N m 1) (lign A Ñ N m 1)
def mold := crimp (truss A N m) (lign A Ñ N m 1)
def duet := (1/2:ℝ) • (crimp (truss A N m) (glow A Ñ N m)+whittle (truss A N m) (mold A Ñ N m) (lign A Ñ N m 1)+whittle (truss A N m) (lign A Ñ N m 1) (mold A Ñ N m))
variable {A Ñ N m}
lemma burnt (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): ∀ j, peat A Ñ N m j 0=0:= fun i=> ordered_spurs h p i g
lemma rays_succ (i j:ℕ): peat A Ñ N m (i+1) j= (((i+1:ℕ):ℝ)⁻¹) • (crimp (truss A N m) (peat A Ñ N m i j)+curlJ (truss A N m) (peat A Ñ N m) (peat A Ñ N m) i j):= by unfold peat spurs; rw [tide_rise]
lemma rays_nil (k:ℕ) : peat A Ñ N m 0 k=lign A Ñ N m k:= by unfold peat spurs; rw [tide_zero]
lemma mold_oc (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): peat A Ñ N m 1 1=mold A Ñ N m:=by rw [rays_succ,vanish_cross (burnt g h p),rays_nil]; simp [mold]
lemma glow_oc (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): peat A Ñ N m 1 2=glow A Ñ N m:=by rw [rays_succ,once_cross (burnt g h p)]; simp [glow,rays_nil]
lemma duet_oc (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): peat A Ñ N m 2 2=duet A Ñ N m:=by
   rw [show (2:ℕ)=1+1 from rfl,rays_succ]; rw [show 1+1= (2:ℕ) from rfl,once_cross (burnt g h p)]; unfold duet
   -- antidiagonal
   rw [show Finset.antidiagonal (1:ℕ)={(0,1),(1,0)} by decide]
   norm_num [glow_oc g h p,mold_oc g h p,rays_nil,Finset.sum_range_succ]; abel
-- raw term at positive rank
lemma amplitude (i j:ℕ): freshet A Ñ N m (i+1) (j+1)= - amberK A Ñ N m (i+1) (j+1) := by unfold freshet season tinge; simp [flatPal,uband,shine_dark (show 0≠j+1 by omega),amberK]
lemma quarters (g:G.Simple)(h:LocalRatio Ñ)(p:m<N):
    freshet A Ñ N m 2 2 = -(scoop ((lign A Ñ N m 2) 2+glow A Ñ N m 2+duet A Ñ N m 2)):=by
   rw [show 2=1+1 from rfl, amplitude]; rw [early_sum _ _ 3 g h p (by omega) (by omega)]
   norm_num [Finset.sum_range_succ,rays_nil,glow_oc g h p,duet_oc g h p]
lemma back_fee (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): coeff 2 (ratioHigh A Ñ N m)= (1/2:ℝ)* coeff 2 (pitch A Ñ N m):=by
   let R:= pitch A Ñ N m
   let B:= ratioHigh A Ñ N m
   have he:constantCoeff R=1:=angle_tilt g h p; have ht : evenC R:= (perch A Ñ g h p).parityC
   have hp: constantCoeff B=1:= back_cc he; have hz:= ht 1 (by decide)
   have hb: evenC B:= even_back he ht
   have H:= signal_square R he 2 (by omega)
   change coeff 2 B=(1/2:ℝ) * ((∑ i∈(Finset.range 3).erase 0, coeff i R*coeff (2-i) (B^i))-∑ j∈ ((Finset.antidiagonal 2).erase (0,2)).erase (2,0), coeff j.1 B *coeff j.2 B) at H
   change coeff 2 B=(1/2:ℝ)*coeff 2 R; rw [H, show ((Finset.antidiagonal 2).erase (0,2)).erase ((2,0):ℕ×ℕ)={(1,1)} by decide, show (Finset.range 3).erase 0={1,2} by decide]
   norm_num [hz,hb 1 (by decide),hp]

theorem beads (g:G.Simple)(h:LocalRatio Ñ)(p:m<N):
    actionW A Ñ N m 1 = shine (-(scoop (lign A Ñ N m 1 3))) ∧
    coeff 2 (ratioHigh A Ñ N m)= (1/2:ℝ)*readSun (-(scoop ((lign A Ñ N m 2) 2+glow A Ñ N m 2+duet A Ñ N m 2))) := by
    have he := catchment A Ñ g h p.le
    constructor
    · ext1 i; by_cases hb: 3=i
      · subst i; rw [conduct A Ñ p,Blue.mix]; simp [Finset.sum_range_succ, show constantCoeff (ratioHigh A Ñ N m)=1 from back_cc (angle_tilt g h p), show freshet A Ñ N m 1 3= - scoop _ from (amplitude 0 2).trans (by rw [virgo g h p]), lop, show freshet A Ñ N m 0=_ from (perch A Ñ g h p).lead, shine_dark,shine_lit]
      rw [shine_dark hb]; by_cases H:i≤2; swap; · exact he.rank 1 i (by omega)
      by_cases ht:i=1; · subst i; exact he.vanishes _
      exact he.grade 1 i (by omega)
    rw [back_fee g h p, pitch,stellar_read,quarters g h p]
end Bloom
end YM.WilsonCoeffUV.Bank
