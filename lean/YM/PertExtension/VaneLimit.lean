import YM.PertExtension.AirJourney

/-! Joint difference-symbol samples represented before any contraction with
counterterm stencils. This deals with truncation in one common *declared* top
alphabet. The actual fields may require a further address and filtration
calculation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Next.Rank.Beamer Air Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
open Projection Configuration
variable {G : Gauge} {q : ℕ+} {n M d : ℕ}
local notation "reg" => (atTop : Filter ℕ)

lemma ctrlFinite_pair (d : ℕ) (M) : Finite {p : Degree G//attends d M p} := by
  let A:= {p : Degree G//attends d M p}
  have hs (x:A): x.val.degree<d+1 ∧ street x.val.point≤M := by
       obtain (⟨h,he⟩|⟨h,he⟩):=x.property; exact ⟨by omega,by rw [street,h];simp⟩; exact ⟨by omega,he⟩
  let s:ℕ+:=⟨M+1,by omega⟩
  have h (x:A):x.val.point∈room s 1:=by
       have h i : (x.val.point i).natAbs ≤ M:= (Finset.single_le_sum (s:=Finset.univ) (f:=fun i:Axis=>(x.val.point i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans (hs x).right
       exact Finset.mem_Icc.mpr ⟨fun i=>show -((↑(1*(M+1)):ℤ)) ≤ _ from by have :=h i;omega,fun i=>show _≤(1*(M+1):ℤ) from by have :=h i; omega⟩
  let V:= (k:Fin (d+1))× ((Fin k.val→Axis) × PlaqAxes × G.ColorIndex × ↥(room s 1))
  let f (x:A): V:= ⟨⟨x.val.degree,(hs x).1⟩,x.val.layout,x.val.a,x.val.paint, ⟨x.val.point,h x⟩⟩
  let decode (w:V):Degree G:= ⟨w.2.2.1,w.2.2.2.1,w.2.2.2.2,w.1,w.2.1⟩
  have hi : Function.Injective f:=fun x y e=>Subtype.ext (congr_arg decode e)
  exact Finite.of_injective f hi

section Fixed
variable (d) {x : Points n} (hx:x∈conf n)(a b:Fin n)(hne:a≠b)

private def currency (r:ℝ)(u v:Degree G) (X:Bridge G):= amount r u * amount r v * mourn (gesture u) (gesture v) X
private lemma norm_absorb {r:ℝ}(r₁:r≥0)(u v:Degree G) (X:Bridge G):
    ‖currency r u v X‖=amount r u * amount r v * ‖mourn (gesture u) (gesture v) X‖ := by
  rw [currency,norm_mul,norm_mul,Real.norm_of_nonneg ?_,Real.norm_of_nonneg ?_]
  exact pow_nonneg r₁ _
  exact pow_nonneg r₁ _
lemma current_bound (u v:Degree G):∃ B:ℝ,∀ r≥(1:ℝ),‖currency r u v (Prayer.collect d hx r G a b)‖ ≤ B:= by
    let A (i j:KeyIn G d):= ((currentX hx G d).cov (a,i) (b,j)).re
    refine ⟨∑ i:KeyIn G d,∑ j,‖A i j‖*(‖gesture u (tester i.val)‖* ‖gesture v (tester j.val)‖),fun r hr=> ?_⟩
    rw [currency,Prayer.collect, Prayer.at_curve]
    apply (norm_sum_le ..).trans
    refine sum_le_sum (fun i hi=>(norm_sum_le ..).trans (sum_le_sum (fun j hj=>?_)))
    rw [norm_mul,norm_mul]; change ‖A i j‖*(_ *_)≤‖A i j‖*( _*_) 
    exact mul_le_mul_of_nonneg_left (mul_le_mul (Prayer.towering u hr i) (Prayer.towering v hr j) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

variable (hq:1<q.val)(u v : ℕ→Cover)
structure Adrift : Prop where
  gap : Tendsto (fun t=>epsilon q t • mapZ (u t-v t)) reg (𝓝 (x a-x b))
  image : ∃ r,0<r∧∀ i c e,∀ᶠ k in reg,Screen r (side q k) (reflectedOffset (u k) (v k) c i e)

variable (ha:Adrift (x:=x) (q:=q) a b u v)
-- subtract one target covariance in each slot before lifting truncations
def currentError (t:ℕ) : Bridge G:= echo (side q t) (u t) (v t)-Prayer.collect d hx (magnify q t) G a b
include hx hne hq ha
private lemma current_real (p s:Degree G)(t) : currency (magnify q t) p s (currentError (q:=q) d hx a b u v t) =
    currency (magnify q t) p s (echo (side q t) (u t) (v t)) - currency (magnify q t) p s (Prayer.collect d hx (magnify q t) G a b) := by rw [currency,currentError,map_sub,mul_sub];rfl

def valueGrid (p s:Degree G) (t:ℕ):= currency (magnify q t) p s (currentError (q:=q) d hx a b u v t)
lemma echo_leading (p s:Degree G) :
    Tendsto (fun t=>currency (magnify q t) p s (echo (side q t) (u t) (v t))) reg (nhds (Prayer.light p s (x a) (x b))):=by
    have hz:x a≠ x b:=(show Injective (WithLp.ofLp x) from hx) |>.ne hne
    obtain ⟨r,hr,h⟩:=ha.image
    apply Tendsto.mono_right (price_total hq (show x a-x b∈ Maxwell.away from sub_ne_zero.mpr hz) ha.gap p s hr h)
    exact le_of_eq (congr_arg nhds (Prayer.glisten p s (x a) (x b) hz)) -- named

lemma mismatch_limit (p s:Hub G d 0) : Tendsto (valueGrid (q:=q) d hx a b u v p.val s.val) reg (𝓝 0):= by
    let C:=currentX hx G d
    let D:=∑ i:KeyIn _ d,∑ j,‖C.cov (a,i) (b,j)‖
    let L:= Prayer.light p.val s.val (x a) (x b)
    let r t:= magnify q t
    have hr k : 1≤r k:=one_le_pow₀ (Nat.one_le_cast.mpr hq.le)
    let F t:= currency (r t) p.val s.val (Prayer.collect d hx (r t) G a b)
    let X t:= currency (r t) p.val s.val (echo (side q t) (u t) (v t))
    have hf : Tendsto F reg (𝓝 L):=by
       have he:=Prayer.fence p s (n:=n)
       obtain ⟨c,hc,h⟩:=he
       have hD:= fun (i j) => show ‖C.cov (a,i) (b,j)‖≤D from (Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>‖C.cov (a,i) (b,j)‖) (fun u _=>norm_nonneg _) (mem_univ j)).trans (Finset.single_le_sum (s:=Finset.univ) (f:=fun i:KeyIn G d=>∑ j:KeyIn G d,‖C.cov (a,i) (b,j)‖) (fun u _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (mem_univ i)) -- adjust lambda
       have hx := h x hx a b hne D (show 0≤D from Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (fun i j=>(Complex.abs_re_le_norm _).trans (hD i j))
       have hv:=scale_inv hq |>.const_mul (c*D)
       have hb : Tendsto (F-fun _=>L) reg (𝓝 0):=squeeze_zero_norm' (a:=fun t=>c*D/r t) (Eventually.of_forall fun t=>(le_div_iff₀' (zero_lt_one.trans_le (hr t))).2 (hx (r t) (hr t))) ?_
       convert! hb.add_const L using 2 <;> simp
       simpa only [mul_zero,div_eq_mul_inv,Pi.inv_apply] using! hv
    have he := (show Tendsto X reg (nhds L) from echo_leading hx a b hne hq u v ha p.val s.val).sub hf
    rw [sub_self] at he; exact he.congr (fun t=> (current_real d hx a b hne hq u v ha p.val s.val t).symm)

lemma mismatch_bounded (p s:Degree G) : ∃ C:ℝ,∀ᶠ t in reg,‖currency (magnify q t) p s (currentError (q:=q) d hx a b u v t)‖≤C:=by
    have he:= echo_leading hx a b hne hq u v ha p s; let L:= Prayer.light p s (x a) (x b)
    obtain ⟨C,h⟩:=current_bound d hx a b p s
    have hP:∀ᶠ t:ℝ in 𝓝 ‖L‖,t≤ ‖L‖+1:=ge_mem_nhds (lt_add_one _)
    refine ⟨‖L‖+1+C, (he.norm.eventually hP).mono fun t ht=>?_⟩
    have hr:1≤magnify q t:=one_le_pow₀ (mod_cast hq.le)
    rw [current_real d hx a b hne hq u v ha]; exact (norm_sub_le ..).trans (add_le_add ht (h _ hr))
end Fixed
end YM.PertExtension.LatticePT
