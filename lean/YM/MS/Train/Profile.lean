import YM.MS.Train.Hosts
/-!
# exact $R$ generator at physical scale intertwines, not bookkeeping shortcut
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{K L E:Mob G}{f g:Coat G}{b:Bool}{t q:ℤ}{U V:Rip G}{k m n h ℓ:ℕ}{i:ℂ}{s:ℝ}
-- extension valid only eventually and only actual port.
def swamp (U:Rip G) : MH (Coat G) := tapeL fun i=> feeD i • port i U
def CycleN (U:Rip G) : MH (Flats G):= blast 1 (swamp U)
def TreeN (U:Rip G) : Signal.Pair (Flats G) := explode (tapeB ( squad U))
def QN (G:Gauge): MH (Flats G):= blast 0 (tapeL (fun _=> sweepQ ( Wick.Q G)))
def unitC (x:ℂ)(y:ℝ)(U:Rip G): MH (Mob G):= tenorK x y • port x U
variable {a:ℂ}
lemma weightAdd (m n:ℕ)(x:ℂ)(y:ℝ) : Pearl.weight x (m+n) y = weight x m y * weight x n y := by unfold Pearl.weight; rw [show toll x (m+n)= toll x m+toll x n from ?_, amount_add]; unfold toll; push_cast; ring
lemma cycle_bind (x:ℂ)(h:x∈Town)(hu:Knot false U)(hp:Form0 false (f x))(he:a-4=(n:ℂ)-m)(s y:ℝ)(k:ℕ): hikeP x m (k+1) y s ((swamp U) f x)= unitC x y (pulse a s U) ( hikeP x n k y s (f x)):= by
    -- algebra x. V interp
    let v:= vamp x n k; let L := pulse a s U; let b := vamp x m (k+1); have hz: vamp x m (k+1)= a+v-4-2*x:= by unfold v vamp toll; push_cast; linear_combination -he
    unfold hikeP unitC; simp only [LinearMap.smul_apply,map_smul, show ((swamp U) f x)=feeD x • port x U (f x) from rfl, ← cert]; -- simp pass ordering
    rw [port_spec h _ hu hp, cert,cert,port_spec h _ (fze hu a s) (fseed hp v s), air_ocean hp.price hu.price,hz,weightAdd]; unfold v tenorK; rw [smul_smul,smul_smul,mul_assoc]
lemma tree_bind (x:ℂ)(hu:reverseF U) (K L:Mob G){a b n:ℕ}{d:ℂ}(h:d-(a:ℂ)-b=-(n:ℂ))(s y:ℝ)(m k:ℕ): hikeP x n (m+k) y s ( arbor U K L)=arbor (pulse d s U) ( hikeP x a m y s K) (hikeP x b k y s L):= by
    unfold hikeP; simp only [← schedule,map_smul,LinearMap.smul_apply]; simp_rw [schedule]; rw [ air_tree _ _ _ s hu]; simp_rw [weightAdd,mul_smul]; rw [ smul_comm (Pearl.weight x k y) ]; congr 3; unfold vamp toll; push_cast; linear_combination -h -- uncertainty
lemma QB (x:ℂ)(m k:ℕ)(y s:ℝ)(F:Mob G): hikeP x (m+1) k y s ( portZ (Q G) F)=portZ (Q G) (hikeP x m k y s F):= by unfold hikeP; simp only [← upcoming,map_smul]; simp_rw [ upcoming, pole_amp _ (lawQ G)]; congr 2; unfold vamp; push_cast; abel
lemma page_sum (S:Finset I)(F:I→ Flats G)(n:ℕ)(y t:ℝ): Parade (∑ i∈ S,F i) n y t= ∑ i∈ S,Parade (F i) n y t := by classical induction S using Finset.induction with| empty=> simp [pageZ]| insert p s hp ih=> rw [Finset.sum_insert hp, Finset.sum_insert hp, page_add,ih]
lemma length_at (h:i∈ Town)(hU:Knot false U)(hx:∀ j,Form0 false (F j i))(he:a-4=(n:ℂ)-m)(s y:ℝ): Parade (CycleN U F) m y s i=unitC i y (pulse a s U) ( Parade F n y s i):= by
    unfold CycleN; rw [blap,Finsupp.sum,page_sum]
    conv_rhs=> rw [Parade,Finsupp.sum]
    simp_rw [Finset.sum_apply,page_sl,map_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; exact cycle_bind i h hU (hx j) he s y j
lemma tree_at (hp:reverseF U)(he:a-(ℓ:ℂ)-n=-(m:ℂ))(y s:ℝ)(i:ℂ): Parade (TreeN U F X) m y s i=arbor (pulse a s U) ( Parade F ℓ y s i) ( Parade X n y s i):= by
    unfold TreeN; rw [explodeL]; unfold Finsupp.sum; simp_rw [page_sum, Finset.sum_apply,page_sl]
    conv_rhs=> rw [ Parade,Parade,Finsupp.sum,Finsupp.sum]
    simp_rw [← schedule,map_sum,LinearMap.sum_apply]; -- pass
    conv_rhs=> rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj=> Finset.sum_congr rfl fun k hk=> ?_; rw [add_comm]; exact tree_bind i hp (F j i) (X k i) he s y j k
lemma Q_at (m:ℕ)(s y:ℝ)(i:ℂ): Parade (QN G F) (m+1) y s i=portZ (Q G) (Parade F m y s i):= by
    unfold QN; rw [blap,Finsupp.sum,page_sum,Finset.sum_apply]
    conv_rhs=> rw [ Parade,Finsupp.sum,← upcoming,map_sum]
    exact Finset.sum_congr rfl (fun j _=>by rw [page_sl, Nat.add_zero]; exact QB i m j y s _)
end YM.MS.Train
