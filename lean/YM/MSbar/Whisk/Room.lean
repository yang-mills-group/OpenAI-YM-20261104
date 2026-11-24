import YM.MSbar.Whisk.Barrel
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao PowerSeries Omnibus
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ][DecidableEq σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d j:ℕ} {S r a b t u v B D E :ℝ}{f g F G : PowerSeries (Pot σ)}
variable {k k':σ→σ→ℝ}
local notation "J"=> juncture
local notation "µ"=> PowerSeries.coeff
set_option quotPrecheck false
local notation "K!"=>normalized
variable (H₀:Gain l x a B p k k' b D)
local notation "L"=>Omnibus l x a B p
variable (hf:Kind f)(hg:Kind g)(hF:Kind F)(hG:Kind G)
def ribbon (i:ℕ)(d:ℕ) :=(i+2)*d
local notation "r!"=> ribbon j d
include hf
lemma stands (W:Expanse f j d)(h:q≤d)(k:σ→σ→ℝ): µ q (confect k f) =∑ r∈Finset.range (ribbon j d+1),Ride f k q r:=by
    unfold confect; rw [PowerSeries.coeff_map]; let P':= PowerSeries.coeff q (normalized k f); refine (peal P').trans (sip P' r! ?_); by_contra hP
    have hh: P'≠0:=fun e=> hP (by rw [e,Polynomial.natDegree_zero]; omega); have ha:r! < P'.natDegree:=lt_of_not_ge hP; have hv:Ride f k q P'.natDegree≠0:=by change P'.coeff P'.natDegree≠0; rw [Polynomial.coeff_natDegree];exact Polynomial.leadingCoeff_ne_zero.mpr hh
    have he := ripens (k:=k) hf W P'.natDegree q _ le_rfl h hv; have hk : (j+2)*q≤r!:=Nat.mul_le_mul_left _ h; omega
lemma cohorts (W : Expanse f j d) : Expanse (confect k f) j d := by
    refine ⟨fun i hi=>?_⟩; rw [stands hf W hi]; refine totalDegree_finsetSum_le (fun v hv=>?_); exact cropped hf W v i _ le_rfl hi
-- time of a fixed return

def driver (j d m:ℕ)(b t:ℝ):= (ribbon j d+1:ℕ)*(rail m (ribbon j d) d b t (ribbon j d))
include H₀ hg hF hG
lemma voyage (α: Expanse f j d)(β: Expanse g j d)(γ:Expanse F j d)(δ:Expanse G j d)(hi:∀ q'≤ d,L (m+2*ribbon j d) ξ (µ q' f) (µ q' g) (µ q' F) (µ q' G) t D) (hc:q≤ d) : L m ξ (µ q (confect k f)) (µ q (confect k' g)) (µ q (confect k F)) (µ q (confect k' G)) (driver j d m b t) D:=by
    rw [stands hf α hc,stands hg β hc,stands hF γ hc,stands hG δ hc]
    let p':= ribbon j d; let t':= rail m p' d b t p'
    have hT(i)(hw:i≤p'): L m ξ (Ride f k q i) (Ride g k' q i) (Ride F k q i) (Ride G k' q i) t' D:=by
        have ht:= dawnP H₀ hf hg hF hG p' hi p' le_rfl q hc i hw; simpa only [Nat.sub_self,Nat.mul_zero, Nat.add_zero] using ht
    rw [show driver j d m b t= ∑ i∈range (p'+1),t' from ?_]; exact Omnibus.pooling _ _ _ _ _ _ (fun i hv=> hT i (Nat.lt_succ_iff.mp (mem_range.mp hv)))
    rw [sum_const,nsmul_eq_mul,card_range]; rfl
omit H₀ hg hF hG
lemma cargo (x:Site n)(ha:0≤a)(hc : LoopNet l a p k b)(α:Expanse f j d)(hi:∀ n'≤d,Tokew l a p (m+2*ribbon j d) ξ (µ n' f) t)(hv:q≤d):
     Tokew l a p m ξ (µ q (confect k f)) (driver j d m b t) :=by
   have hp:0 ≤ t:=(hi 0 (by omega)).1
   let H:=driver j d m b t; let d':=m+2*ribbon j d
   have he:Gain l x a 0 p k k b 0 := by
       refine ⟨ha,le_rfl,le_rfl,add_zero a|>.symm ▸ hc,add_zero a|>.symm ▸ hc,?_⟩; rw [sub_self]; refine ⟨le_rfl,fun i=>?_,fun i=>?_⟩<;>simp
   have h (n) (hx:n≤d) : Omnibus l x a 0 p d' ξ (µ n f) (µ n f) (µ n f) (µ n f) t 0:=by
       let k:= µ n f; have hf: Paired l x a 0 p d' ξ k k t 0 t:=by
           refine ⟨add_zero a|>.symm ▸ hi n hx,add_zero a|>.symm ▸ hi n hx,?_⟩; rw [sub_self, mul_zero]; refine ⟨le_rfl,fun x=>?_⟩; rw [_root_.map_zero, mul_zero]; exact Quote.nill le_rfl
       refine ⟨hf,hf,?_⟩; rw [sub_self]; refine ⟨Quote.nill hp,Quote.nill hp, ?_⟩; rw [sub_self,mul_zero];exact Quote.nill le_rfl
   have ht:= voyage he hf hf hf hf α α α α h hv; exact add_zero a ▸ ht.bulk.input
end YM.MSbar.Whisk
