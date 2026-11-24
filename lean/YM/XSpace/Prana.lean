import YM.XSpace.Sanctum
/-!
# Each assignment costs a cubic margin receipt
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Relief Tide Sail Gland Chart2 Octave Season Lattice Chiral MvPolynomial Player Graph3 Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{W:Initialize G}{ι:Type} {a:ι→ℝ}{L:Filter ι} {x y z:ι→Cover} {u v b:E4} {c:Shade.Cut}
local notation "W₁" => G.ColorIndex
local notation "₹" => cover
variable (P Q R:Player W)(g:G.Simple) (x y z w:Cover)(σ:Bool)(k:Name G)
private def arm (X:Toe): ℂ:= (↑(χ P.color k.2 * X (w-x)):ℂ) -- B capsule frame
abbrev margin0 (X:Toe): ℂ:= arm P x w k X * pair Q R g w y z (stance σ k)
abbrev mio := O P g σ k.1 -- cannot λ pref
abbrev margin := margin0 P Q R g x y z w σ k (mio P g σ k)
abbrev τ (x y z:Cover)(F:Toe):= ∑ i:Axis,∑ j:Axis,q σ k.1 i j* Trail x y z F (Q.M g i) (R.M g j)
abbrev Φ (x y z w:Cover)(F:Toe):=∑ i:Axis,∑ j:Axis, q σ k.1 i j * Form x y z F (Q.M g i) (R.M g j) w
def heel : ℝ:=χ P.color k.2*br k.2 Q.color R.color
lemma marginal (X:Toe): margin0 P Q R g x y z w σ k X=↑(heel P Q R k* Φ Q R g σ k x y z w X):=by
  unfold margin0 arm; rw [needlework,← Complex.ofReal_mul]; apply congr_arg ((↑):ℝ→ℂ); unfold heel Φ Form print; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
lemma strap (x y z w:Cover): feet x y z (P.origin g) (Q.origin g) (R.origin g) (aimed G σ k) w = margin P Q R g x y z w σ k + margin Q P R g y x z w σ k+margin R P Q g z x y w σ k:=by
  let f:= Relief.core σ k.1 k.2 w; have he (P:Player W)(z:Cover): col f (P.ask g z)= arm P z w k (mio P g σ k):=congr_arg ((↑):ℝ→ℂ) (canon_pairs ..); let A:=P.ask g x; let B:=Q.ask g y; let C:=R.ask g z; let p:= Trace.volume w (stance σ k); change read A B C (Trace.volume w _)=_; rw [aimed,map_mul (Trace.volume w),rootleg, money]; unfold margin margin0; rw [← he, ← he,← he]; simp_rw [pair_at]; change peek G (Ξ A (Ξ B (Ξ C (harp f * p))))= col f A * _ + col f B* _ + col f C*_; -- detect
  simp only [ξ_mul,ξ_harp,ξ_zero,map_add,map_mul,zero_add,peek_leg,zero_mul,add_zero,peek_C]; -- align A,B,C defeq
  unfold A B C p; ring
variable {D:Toe}
lemma φs (H:D∈Terrain 4): Summable fun w:Cover=> Φ Q R g σ k x y z w D:=by refine summable_sum (fun i (_:i∈Finset.univ)=> summable_sum (fun j (_:j∈Finset.univ)=>?_ )); exact (form_sum H (Q.α₀ g i) (R.α₀ g j) (by norm_num) x y z).mul_left _
lemma φτ (H:D∈Terrain 4): (∑' w: Cover,Φ Q R g σ k x y z w D)=τ Q R g σ k x y z D:=by unfold Φ τ; have ht(i j:Axis):= (form_sum H (Q.α₀ g i) (R.α₀ g j) (by norm_num) x y z).mul_left (q σ k.1 i j); rw [Summable.tsum_finsetSum (fun i (_:i∈Finset.univ)=> summable_sum (fun j (_:j∈Finset.univ)=> ht i j))]; apply Finset.sum_congr rfl; intro i _; rw [Summable.tsum_finsetSum (fun j _=>ht i j)]; simp_rw [tsum_mul_left]
lemma strapS (x y z:Cover){X:Toe}(h:X∈Terrain 4): Summable fun w:Cover=> margin0 P Q R g x y z w σ k X:=by simp_rw [marginal]; exact Complex.summable_ofReal.mpr ((φs Q R g x y z σ k h).mul_left _)
lemma revenue (x y z:Cover){X:Toe}(h:X∈Terrain 4): (∑' w:Cover, margin0 P Q R g x y z w σ k X)= (↑(heel P Q R k*τ Q R g σ k x y z X):ℂ):=by simp_rw [marginal,← Complex.ofReal_tsum,tsum_mul_left,φτ Q R g _ _ _ σ k h]
lemma strapT (x y z:Cover): Uplands x y z (P.origin g) (Q.origin g) (R.origin g) (aimed G σ k) = (∑' w:Cover,margin P Q R g x y z w σ k)+(∑' w:Cover,margin Q P R g y x z w σ k)+∑' w:Cover, margin R P Q g z x y w σ k:=by
  unfold Uplands; simp_rw [strap P Q R g σ k
  ]; let f:= fun (P Q R:Player W)(x y z:Cover)=> strapS P Q R g σ k x y z (origin₄ P g σ k.1); rw [((f P Q R x y z).add (f Q P R y x z)).tsum_add (f R P Q z x y),(f P Q R x y z).tsum_add (f Q P R y x z)]
end YM.XSpace.Finale
