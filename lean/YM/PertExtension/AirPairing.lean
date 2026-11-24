import YM.PertExtension.SpectralCurl

/-! Inverting the exact quadratic constraint using a full torus curl response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.LatticePT
namespace Projection
open MeasureTheory Filter Maxwell Next Next.Rank.Perch Next.Rank.Radian Next.Rank Topology Set Real Metric Lattice Next.Rank.CellsInt
open Next.Rank.Beamer Orb Band Air Orbit
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical RealInnerProductSpace
variable {G : Gauge}{n:Side}

abbrev weight (p:Face (Per n)) (k:Site n): Ribbon:=brief (backward k) p.2.val.1 p.2.val.2
abbrev perTone (k:Site n)(z:Ribbon)(e:Edge (Site n)) := z e.2*tone e.1 k

def wrinkle (p:Face (Per n)) (k:Site n):ℂ:= (nV n)⁻¹ * tone (-p.1) k / (location (frequency k):ℝ)
def lighting (p:Face (Per n)) (k:Site n) : Links (Per n) ℂ:= fun e=>wrinkle p k * perTone k (weight p k) e
def shining (p:Face (Per n)) : Links (Per n) ℂ:= fun e=>∑ k:Site n,lighting p k e
def disk (c:Links (Per n) ℂ)(p : Face (Per n)):=Orb.Curl c p.1 p.2.val.1 p.2.val.2
lemma disk_shining (y p:Face (Per n)):
    disk (shining y) p = ∑ k:Site n,disk (lighting y k) p:= by unfold disk shining Orb.Curl; simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
lemma disk_aug (y p:Face (Per n))(k:Site n): disk (lighting y k) p=wrinkle y k * disk (perTone k (weight y k)) p:=by unfold disk Orb.Curl lighting; ring
lemma disk_tone (z:PlaqAxes)(x:Site n)(k:Site n)(t): disk (perTone k t) (x,z)=tone x k * wedge (gradient k) t z.val.1 z.val.2:= curl_mode ..
protected lemma disk_forward (A:Links (Per n) ℂ)(z:PlaqAxes)(k:Site n): Band.fourier (fun x=>disk A (x,z)) k = wedge (backward k) (current A k) z.val.1 z.val.2:= by unfold disk; exact forward_curl k A z.val.1 z.val.2
lemma mode_identity (A:Links (Per n) ℂ)(z:PlaqAxes)(k:Site n)(t) :
 (∑ x:Site n,disk (perTone k t) (x,z)*disk A (x,z)) =
    (wedge (gradient k) t z.val.1 z.val.2)*(wedge (backward k) (current A k) z.val.1 z.val.2):=by
  let c:=wedge (gradient k) t z.val.1 z.val.2; let B (x):=disk A (x,z)
  calc
    _ = c*(Band.fourier B k) := by unfold Band.fourier; rw [Finset.mul_sum];refine Finset.sum_congr rfl fun x _=> ?_; rw [disk_tone];dsimp only [c,B];ring
    _ = _ := by unfold B; rw [Projection.disk_forward] <;> rfl
lemma mode_test (A y)(k:Site n):
    (∑ p:Face (Per n), disk (perTone k (weight y k)) p*disk A p) = (location (frequency k):ℝ) * Band.fourier (fun x=>disk A (x,y.2)) k:=by
  let z:= weight y k ;let V (p:Face (Per n)) := disk (perTone k z) p*disk A p
  let d:= gradient k; let t:= backward k;let w:=current A k
  let f:=fun x=>disk A (x,y.2)
  calc
     _ = ∑ p:PlaqAxes,∑ x:Site n,V (x,p) := (Fintype.sum_prod_type V).trans Finset.sum_comm
     _ = ∑ p:PlaqAxes,(wedge d z p.val.1 p.val.2)*(wedge t w p.val.1 p.val.2) := Finset.sum_congr rfl fun p _=> mode_identity ..
     _ = (∑ i:Axis,d i*t i)*(t y.2.val.1*w y.2.val.2-t y.2.val.2*w y.2.val.1) := Air.expands d t w ..
     _ = _:= by change (∑ i:Axis,gradient k i * backward k i) * wedge t w y.2.val.1 y.2.val.2=_;rw [marked_sum, Projection.disk_forward] <;> rfl
lemma scalar_weak (A:Links (Per n) ℂ)(y:Face (Per n))(k:Site n):
   (∑ p:Face (Per n), disk (lighting y k) p*disk A p) = ((nV n)⁻¹ * tone (-y.1) k) * Band.fourier (fun x=>disk A (x,y.2)) k:=by
    let c:= wrinkle y k; let z:=weight y k;let h (p:Face (Per n)):= disk (perTone k z) p*disk A p
    have hp p : disk (lighting y k) p * disk A p= c*h p:=(congr_arg₂ (·*·) (disk_aug y p k) rfl).trans (mul_assoc ..)
    have hv:= mode_test A y k
    let F:=fun x=>disk A (x,y.2)
    change (∑ p:Face (Per n),h p)=((location (frequency k):ℝ):ℂ)* Band.fourier F k at hv
    calc
       _ = c*(∑ p:Face (Per n),h p):= by rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _=>hp i
       _ = _:= by
          rw [hv];by_cases hx:k=0
          · unfold F; rw [Projection.disk_forward]; simp only [hx, wedge, backward]; have heZ (x:Site n):tone x (0:Site n)=1:=by rw [tone_swap, tone_zero] -- patch
            simp only [heZ];ring -- `tone_swap` loop
          unfold c wrinkle
          have hc : ((location (frequency k):ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (mode_mass hx).ne'
          field_simp; rfl
lemma disk_associate (A:Links (Per n) ℂ)(y p:Face (Per n)): disk (shining y) p * disk A p =
   ∑ k:Site n,disk (lighting y k) p * disk A p:= by rw [disk_shining, Finset.sum_mul]
lemma scalar_law (A:Links (Per n) ℂ)(y:Face (Per n)) :
   (∑ p:Face (Per n), disk (shining y) p * disk A p)=disk A y:=by
   let T (k:Site n)(p:Face (Per n)):= disk (lighting y k) p* disk A p
   let f(x):=disk A (x,y.2);let Q k:=tone (-y.1) k * Band.fourier f k
   have he := reconstruction n f y.1
   have h'' (k): (∑ p:Face (Per n),T k p)= (nV n)⁻¹ * Q k:= (scalar_weak A y k).trans (mul_assoc ..)
   calc
      _= ∑ p:Face (Per n),∑ k:Site n,T k p := Finset.sum_congr rfl fun i _=> disk_associate ..
      _=(nV n)⁻¹*(∑ k: Site n,Q k):= by rw [Finset.sum_comm,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>h'' i
      _= _:=he
end Projection
end YM.PertExtension.LatticePT
