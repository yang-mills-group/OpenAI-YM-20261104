import YM.MS.Pearl.Broach
import YM.MS.Pearl.Knot
/-!
# p-shift valuations at each Laurent sector
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W X F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ}{s:ℝ}
variable {f g: ℂ→ Mob G}
lemma Rub (h:Live f)(n:ℕ): Pick n f (ruby f n) := by rw [ruby,dif_pos h]; exact Classical.choose_spec (given h n)
lemma chosen (h:Pick n f F): F=ruby f n:= h.unique ( Rub h.live _)
lemma ruby0 (n:ℕ): ruby (G:=G) 0 n=0:= by apply Eq.symm (chosen (f:=0) ?_); simpa only [zero_smul] using ( Rub (G:=G) Live.zero n).static 0
-- shape functions

def gNat (ℓ:ℕ):ℝ:= -2*ℓ
def ley (ℓ i:ℕ)(y:ℝ): ℂ:= ((y*gNat ℓ :ℝ):ℂ)^i/(i.factorial:ℂ)
-- particular forms characteristic pressure
lemma cubic (x:ℂ)(ℓ:ℕ)(y:ℝ): weight x ℓ y=Complex.exp ((y*gNat ℓ:ℝ)*x):= by unfold weight amount toll gNat; congr 1; push_cast; ring -- parse
lemma ew (x:ℂ)(m h:ℕ)(y t:ℝ)(f:Mob G): hikeP x h m y t f=weight x m (y+t) • plow (-(h:ℂ)) t f:= by unfold hikeP; rw [vamp, shift]; unfold weight; rw [amount_time,mul_smul]
lemma chem (i ℓ:ℕ)(y:ℝ): charm i (fun x=> weight x ℓ y)=ley ℓ i y:= by simp_rw [cubic,ley,chill]
def priceY (n m ℓ:ℕ) (v:ℂ→ Mob G)(y:ℝ): Mob G:= ∑ i∈ Finset.range (n+1), ley ℓ i y • ruby (paid m v) (n-i)
lemma lexP (hp:altitude m f)(h ℓ n:ℕ)(y t:ℝ): Pick n (paid m fun i=> hikeP i h ℓ y t (f i)) (plow (-(h:ℂ)) t (priceY n m ℓ f (y+t))):= by
    let c := -(h:ℂ); let G := plower (G:=G) c t; let g := paid m f; let x(i:ℂ):= weight i ℓ (y+t); have he: Forest (disc 1) x:= by unfold x; simp_rw [cubic]; exact fun i hi=> by fun_prop
    obtain hm:= Stars (n:=n) he zero_lt_one (fun i=>( Rub hp i).mount c t); simp_rw [show charm _ x = ley _ _ _ from chem _ ℓ (y+t)] at hm -- has implicit order problem?
    unfold priceY; rw [← cert,map_sum]; simp_rw [map_smul,cert]; refine hm.congr (EventuallyEq.of_eq ?_); funext z; rw [paid,ew]; change x z • G _= _^m • x z • G _ ; rw [smul_comm, paid, map_smul]; -- ordering
lemma emmer (h:mer f)(h' ℓ:ℕ)(y t:ℝ): mer (fun i=>hikeP i h' ℓ y t (f i)) := by obtain ⟨n,h⟩:= h; exact ⟨ _,(lexP h h' ℓ n y t).live⟩
lemma arrive (hp:altitude m f)(hv:∀ᶠ i in dotty, Mell.Trail (f i) (g i) (vamp i h ℓ)): paid m g=ᶠ[dotty] (fun i=> burn (-(h:ℂ)) (paid m f i) + (gNat ℓ:ℂ) • paid 1 (paid m f) i):= by
    filter_upwards [pay_price hp,hv] with i hi hv; unfold paid; rw [burn_unique hv hi,vamp,burn_raise _ hi,burn_mul _ _ hi,smul_add, pow_one]; simp only [smul_smul,toll,gNat]; push_cast; rw [show i^m*(-2*i*ℓ)= (-2*ℓ)*(i*i^m) by ring]
lemma R_prev0 (hp:altitude m f)(hv:∀ᶠ i in dotty,Mell.Trail (f i) (g i) (vamp i h ℓ)): Pick 0 (paid m g) ( burn (-(h:ℂ)) (ruby (paid m f) 0)):= by
    have ht:Pick 0 ((gNat ℓ:ℂ) • paid 1 (paid m f)) 0:= by convert Lift.static (alu (Rub hp 0)) (gNat ℓ:ℂ) using 1; rw [smul_zero]; rfl -- convert?
    simpa only [add_zero] using Pick.congr ((burn_pick (Rub hp 0) (-(h:ℂ))).add ht) (arrive hp hv).symm
lemma R_prev (hp:altitude m f)(hv:∀ᶠ i in dotty,Mell.Trail (f i) (g i) (vamp i h ℓ))(n:ℕ): Pick (n+1) (paid m g) (burn (-(h:ℂ)) (ruby (paid m f) (n+1)) + (gNat ℓ:ℂ) • ruby (paid m f) n) := ((burn_pick (Rub hp _) _).add ((move (Rub hp n)).static _)).congr (arrive hp hv).symm
end YM.MS.Pearl
