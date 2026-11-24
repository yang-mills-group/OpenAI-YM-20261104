import YM.FVA2.Teller.Where
/-!
 # Euler–Tad projection identities for highest-rank sector

 Stratify by $ω \le h$, all dimensions at once. Use in `Industry.lean`.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Landau MS.Arts MS.Arc MS.Plane.Wire MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Alps MS.Garment MS.Color
open _root_.YM.MS.Shine MS.Hem MS.Hem.Mell MS.Train MS.Pearl MS.Motif MS.Heat.Signal MS.Book MS.Book.Convolve MS.Garment.Wave MS.Garment.Wick
open Teller
open scoped Topology ContDiff Interval
variable {G:Gauge}{n d r k ℓ m:ℕ}{F Z: Mob G}{x:ℂ}{Y H:ℝ→Mob G}
open Alps.Bench.Forest
lemma pay_t {f:ℝ→ℂ}(h:ContDiff ℝ ∞ f)(k:ℕ): reading k (loadC f x)=(x+k) * reading k f:= by
    let ιr(t:ℝ):ℂ:= (t:ℂ); have hV : loadC f x=(fun u=> x*f u+ ιr u * deriv f u):= by unfold loadC; funext u; congr 1; rw [show fderiv ℝ f u u=u • deriv f u from ?_,Complex.real_smul]; rw [deriv,← map_smul]; simp
    have he(i):reading i ιr= if (1:ℕ)=i then 1 else 0:= by obtain h:= Plane.read_pow (j:=i) (1:ℂ) 1; simpa only [pow_one,Complex.real_smul,mul_one] using h
    have hh:ContDiff ℝ ∞ (deriv f):= ContDiff.deriv' h -- le? inspect
    have hζ:ContDiff ℝ ∞ ιr:=Complex.ofRealCLM.contDiff
    rw [hV, read_add (contDiff_const.mul h) ( hζ.mul hh ), read_const, read_mul hζ hh]; simp_rw [he]
    cases k with
    | zero=> simp
    | succ k=> rw [ Finset.sum_eq_single 1,if_pos rfl,one_mul, Nat.add_sub_cancel_right ]; push_cast; unfold reading; rw [ ← iteratedDeriv_succ',Nat.factorial_succ ]; simp only [Complex.real_smul]; push_cast; generalize iteratedDeriv (k+1) f 0 = u; have hk:( k.factorial:ℂ )≠0:= (by exact_mod_cast Nat.factorial_ne_zero k); have hx:(k:ℂ)+1≠0:= (by norm_cast); field_simp; ring_nf
               · intro b _ hb; rw [if_neg (Ne.symm hb),zero_mul]
               simp
lemma trail_tad (H: Mell.Trail F Z x)(h:kPrice F)(d:ℕ): Tad Z d=(x+d) • Tad F d:= by
    rw [ burn_unique H h ]; funext m l; rcases lt_or_ge (d:ℤ) (mass l) with h1|h1; · rw [t_exc h1,Pi.smul_apply,Pi.smul_apply,t_exc h1,smul_zero]
    let j:= ((d:ℤ)-mass l).toNat; have h2 : mass l+j=d:= by unfold j; omega
    rw [t_bud _ h2, Pi.smul_apply,Pi.smul_apply,t_bud _ h2]; rw [torch_at, torch_at]; change reading j ( fieldVal (burn x F m) _)= (x+d)*_; rw [Pearl.bump h (ray l),pay_t ((h m ℝ _).smooth ())]; have hm: (mass ( ray l ):ℂ)+(j:ℂ)=d:= by rw [mass,ray_dim]; exact_mod_cast h2
    rw [add_assoc, hm]; rfl
-- projection to one rank. `Tad(F)` preserves such vanishing.
lemma spot_tad (F:Mob G)(k r:ℕ): spot (r:ℤ) ( Tad F k )= Tad ( spot r F ) k := by
    funext m l; rcases lt_or_ge (k:ℤ) (mass l) with hx|hx;
    · rw [t_exc hx]; by_cases he:l.length=r <;> first| (rw [spotted (by omega),t_exc hx]) | exact spotsOff (by omega: (l.length:ℤ)≠r)
    let d:= ((k:ℤ)-mass l).toNat; have hD: mass l+d=k:= by unfold d; omega
    rw [t_bud _ hD]; by_cases ht:l.length=r
    · rw [spotted (by omega), t_bud _ hD]; unfold torch; rw [ show fieldVal ( spot (r:ℤ) F m ) _= fieldVal (F m) (ray l) from funext (fun x:ℝ=> spotted (m:=m) (l:=sail (ray l) x) (by simp [ht])) ]
    rw [spotsOff (by omega), torch_at, show (fun p:ℝ=>_)=(0:ℝ→ℂ) from funext (fun p=> spotsOff (F:=F) (i:=(r:ℤ)) (l:=sail (ray l) p) (by simp [ht])) ]; simp [reading]
lemma spot_plow (F:Mob G)(t:ℝ)(u:ℂ)(r:ℕ) : spot (r:ℤ) (plow u t F)=plow u t (spot r F):= by
    funext m l; by_cases ht:l.length=r
    · rw [spotted (by omega)]; dsimp only [plow]; rw [spotted (by simp [sr,ht]) ]
    rw [spotsOff (by omega)]; dsimp only [plow]; rw [spotsOff (by simp [sr,ht]),mul_zero]
lemma white_w (F:Mob G)(k:ℕ) (h:kPrice F)(he:∀ i<k,spot (r:ℤ) (Tad F i)=0): _root_.YM.MS.Shine.Wind (fun t=>plow (-(k:ℂ)) t (spot r F)) atBot (spot r (Tad F k)) := by
    -- prune <k using he.A
    let V:= spot (r:ℤ) F; have ht :kPrice V := Garment.spot_fall h r
    rw [spot_tad]; have hm : Hem.clear k V= V:= by unfold Hem.clear haze; rw [Finset.sum_eq_zero (?_ : ∀ i∈Finset.range k,Tad V i=0), sub_zero]; intro i hi; exact ( spot_tad F i r ).symm.trans (he i (Finset.mem_range.mp hi))
    obtain hQ:= ray_white ht k; simpa only [wood,hm] using hQ
end YM.FVA2.TreeT
