import YM.MSbar.Chord.Octave
import YM.Corona.Spend
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> n.val
-- full oriented. Normalize at end. uses edge-axis1 same both, local regular unwrapped payoff exactly.S & F.
private lemma relative (o x y:S₀)(i:Axis)(hx:10*separation x o < n.val) (hy:10*separation y o < n.val): coord x y i=coord o y i-coord o x i :=by
    have he : lift (y-x)= lift (y-o)- lift (x-o) := by
        apply lift_eq_iff.mpr; refine ⟨?_,fun i=>?_⟩; rw [map_sub,wrap_lift,wrap_lift];abel
        have hv: (lift (x-o) i).natAbs ≤ separation x o:= component_le ..; have hp:(lift (y-o) i).natAbs ≤ separation y o:= component_le ..; simp only [Pi.sub_apply];omega
    unfold coord; rw [he,Pi.sub_apply]; push_cast;rfl
noncomputable def gross (Q:Positions (Primary n G)→Positions (Primary n G)→ℝ)(e:G.Color):=∑ i:Site n,∑ j:Site n,Q (tuner e i) (tuner e j)* coord i j 0^2
variable (s:Signed) (o : Site n) (a b:Face (Per n))(e:G.Color)
local notation "z₀"=> tuner e
-- Generic linear identity, no winding, arbitrary degrees.
abbrev PMap (n:Side)(G:Gauge):= Positions (Primary n G) →ₗ[ℝ] Positions (Primary n G) →ₗ[ℝ]ℝ
variable (F:PMap n G)
local notation "p!"=>queue e n
lemma squareX2 (hs:∀ x:Site n,F (p! (fun _=>1)) (z₀ x)=0∧F (z₀ x) (p! (fun _=>1))=0) (he:∀ i j, F (tuner e i) (tuner e j)≠0 → (10*separation i o < n.val)∧(10*separation j o < n.val)) :
    gross (fun x y=> F x y) e = -2* F (queue e n (fun x=>coord o x 0)) (queue e n (fun x=>coord o x 0)):=by
    let f(i j:Site n):= F (tuner e i) (tuner e j); let h(i:Site n):= coord o i 0; let T:=∑ j: S₀,h j • tuner e j
    have hp : F T T = ∑ i:S₀,∑ j:S₀,f i j *(h i*h j):=by
        have ht:F T=∑ i:S₀,h i • F (tuner e i):=by unfold T; rw [map_sum]; simp_rw [map_smul]
        rw [ht, LinearMap.sum_apply]; refine Finset.sum_congr rfl (fun i _=>?_); change _*(F (tuner e i) T)= _; unfold T; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; unfold f; ring
    let K:=∑ j:S₀,tuner e j; have hk : queue e n (fun _=> (1:ℝ))=K:=by simp [queue,K]
    simp_rw [hk] at hs
    have hx(j) : ∑ i:S₀,f i j=0 :=by have he:=hs j|>.1; unfold K at he; rw [map_sum] at he; simp only [LinearMap.sum_apply] at he; exact he
    have hy(i) : ∑ j:S₀,f i j=0:=by have he:=hs i|>.2; unfold K at he; rw [map_sum] at he; exact he
    let H:=∑ i:S₀, ∑ j:S₀,f i j* coord i j 0^2; have he : H = ∑ i:S₀,∑ j:S₀,(f i j *h i^2+ f i j *h j^2-2*(f i j*(h i*h j))):=by
        refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>?_)); by_cases hz:f i j=0; simp [hz]; rw [relative o i j 0 (he i j hz|>.1) (he i j hz|>.2)]; unfold h; ring
    change H= -2* F T T; rw [he]; simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]; rw [sum_comm (f:=fun i j=> f i j *h j^2)]; simp_rw [← Finset.sum_mul,hx, hy, zero_mul]; simp only [Finset.sum_const_zero,zero_add]; rw [hp]; simp_rw [← Finset.mul_sum]; ring
private lemma locate (s:Signed)(a:Face (Per n)) : separation (affine s 0 a.1) (Face.send s 0 a).1≤2:=by
    simpa only [affine,add_zero] using AnalyticNext.QuarticMatch.Local.Rotate.shorter s a.2 a.1
-- on slots less than n/40 -2
variable (δ:G.Color →ₗ[ℝ] G.Color →ₗ[ℝ]ℝ) {p:ℕ}
noncomputable def formS (s:Signed) (a b :Face (Per n))(δ:G.Color →ₗ[ℝ] G.Color →ₗ[ℝ]ℝ):PMap n G := δ.compl₁₂ (basin s a) (basin s b) -- name lookup
lemma waveS (a b :Face (Per n)) (o:S₀) (z:ℕ)(he:10*(z+4) < n.val) (ha:separation a.1 o≤ z)(hb:separation b.1 o≤ z):
    gross (fun x y=> formS s a b δ x y) e = -2* δ (mark a.2 e s) (mark b.2 e s):=by
    let A:=formS s a b δ; let w:= affine s (0:S₀) o
    have hh(a:Face (Per n))(hx:separation a.1 o≤ z):separation (Face.send s 0 a).1 w ≤ z+2:=by
        apply (separation_triangle _ (affine s (0:S₀) a.1) _).trans; have ht:separation (affine s (0:S₀) a.1) w=separation a.1 o:= spin_separation ..; have hv: separation (Face.send s 0 a).1 (affine s 0 a.1) ≤ 2 := (separation_comm ..).trans_le (locate s a); exact (ht.symm ▸ Nat.add_le_add hv hx).trans_eq (Nat.add_comm ..)
    have hi(a:Face (Per n))(i:S₀)(hx:separation a.1 o≤z) (hp:curlX s a (tuner e i)≠0):10*separation i w < n.val:=by have hV:= hh a hx; have hi :separation i (Face.send s 0 a).1≤1:=(separation_comm ..).trans_le (le_of_not_gt (fun h=>hp (lamp s a e i h))); have hu := separation_triangle i (Face.send s 0 a).1 w; omega
    have hz:4≤n.val:=by omega
    let T:= queue e n (fun x=>coord w x 0); rw [squareX2 w e]; rotate_left; · intro x; change δ (curlX s a _) _=0∧δ _ (curlX s b _)=0; rw [still, still, map_zero,map_zero]; simp
    · intro i j hp; change δ (curlX s a _) (curlX s b _)≠0 at hp; exact ⟨hi a _ ha (by intro h; apply hp; simp [h]),hi b _ hb (by intro h; apply hp; simp [h])⟩
    change _ * δ (curlX s a T) (curlX s b T)=_; rw [show curlX s a T=_ from web s a e w (by have hg:=hh a ha; omega) hz, show curlX s b T=_ from web s b e w (by have hg:=hh b hb; omega) hz]
end YM.MSbar.Midpoint
