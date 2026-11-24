import YM.FormalBulk08.Kemp.Brush

/-! Assembly and real linearity marks. Cost localized only in fine width
and a finite list of slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {p : Side} {V X:Type*} {m j : ℕ} {η A:ℝ}

-- Route at native lattice (includes wrapping).
def banner (s:ℕ)(T:Pot G)(n:Side): Pap (wire G n):= PowerSeries.mk fun e=> ∑ i ∈ Finset.range (s+e+1), facade i (sieve n (T e i))
lemma sail (T:Pot G) (i:ℕ)(h:Young T i)(m p)(n): coeff m (banner i T n)= coeff m (banner (i+p) T n) := by
   unfold banner; simp only [coeff_mk]; apply Finset.sum_subset (Finset.range_mono (by omega)); intro x _ hx
   have hh : T m x=0:= by by_contra he;have ht:= h m _ he;unfold Yield at ht;simp at hx;omega
   rw [hh,sieve_zero,map_zero]
lemma badge (T:Pot G)(h:Young T m)(he:∀ e r,Agate (T e r))(hp:m≤j) (n e r) : rancho (banner j T n) e r=sieve n (T e r) := by
    let K:=banner j T n
    change marble r (coeff e K)=_
    by_cases h':r≤j+e
    · refine facade_unique (marble_agate r _) (sieve_sand n _ (he e r)) ?_; rw [marble_grade]; unfold K; rw [banner,coeff_mk,map_sum, Finset.sum_eq_single r,MvPolynomial.homogeneousComponent_eq_self (facade_grade _ _)]
      · intro b _ hb; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade ..),if_neg (by omega)]
      simp [h']
    have hz : T e r=0:= by by_contra hb; have he:=h e r hb;unfold Yield at he;omega
    rw [hz,sieve_zero,marble_eq_zero_iff]; unfold K; rw [banner,coeff_mk,map_sum]; refine Finset.sum_eq_zero (fun a ha=>?_) ; have hx:= Finset.mem_range.mp ha; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade ..),if_neg (by omega)]
lemma banner_add (m : ℕ)(T S:Pot G)(n:Side)(h:∀ e r,Summable (T e r))(hp:∀ e r,Summable (S e r)):banner m (T+S) n=banner m T n+banner m S n:= by
   ext1 j; unfold banner; simp only [map_add,coeff_mk,Pi.add_apply]; rw [←Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun r _=>?_); rw [(sieve_sub_add _ (h ..) (hp ..)).1,map_add]
lemma banner_zero (G: Gauge)(m:ℕ)(n:Side): banner (G:=G) m 0 n=0:=by ext1; simp [banner]
lemma banner_coin (m : ℕ)(T:Pot G)(a:ℝ)(n:Side): banner m (a • T) n= C (MvPolynomial.C a)*banner m T n:= by
    ext1 e; unfold banner; simp_rw [coeff_C_mul,coeff_mk,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; simp_rw [Pi.smul_apply,sieve_smul,map_smul,MvPolynomial.smul_eq_C_mul]

-- Moving input positions
variable (x : Cover)

def carries {V : Type*}{C : Type*} [AddCommGroup C](x:C)(T:Tile (C×V) j):=jetty (Lotus.tint (-x)) T
lemma carrying {T:Tile (Biglot V) j}(s:Equiv.Perm (Fin j))(h:Agate T)(v) : carries x T (v ∘ s)=carries x T v:=h ((Lotus.tint (-x)) ∘ v) s
lemma mantle_pay {T:Tile (Biglot V) j}{o:Biglot V}(h:Knoxville (fame _) η o T A) : Knoxville (fame _) η (tint x o) (carries x T) A:= by
   refine ⟨h.1,le_trans (le_of_eq ?_) h.2⟩; rw [←Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) (Lotus.tint x)) _]; refine tsum_congr fun v=> ?_
   have he : carries x T (Lotus.tint x ∘ v)=T v:= by unfold carries jetty; rw [show Lotus.tint (-x) ∘ Lotus.tint x ∘ v=v from funext fun j=>Prod.ext (by simp) (by simp)]
   change (Gorge.shine _ (wide (fame V) (Fin.cons (Lotus.tint x o) (Lotus.tint x ∘ v)))*‖carries x T (Lotus.tint x ∘ v)‖ₑ)= _; rw [show carries _ T _=_ from he, ← Fin.comp_cons ]; simp [wide,fame,capD]

lemma wears {T:Tile (Biglot V) j}(m:Side) : sieve m (carries x T)=carries (wrap m x) (sieve m T):= by
    funext v; rw [sieve_i];change _=sieve m T _; rw [sieve_i];rw [←Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) (Lotus.tint x)) _]; refine tsum_congr fun u=>?_
    let w:=wrap m x; let e : Equiv.Perm (Tor m V):=Lotus.tint w
    have hx : e.symm= Lotus.tint (-wrap m x) := by ext t <;> simp [e,w,Lotus.tint]
    have h (t: chain (Biglot V) j):Lotus.drip m ∘ Lotus.tint x ∘ t=e ∘ Lotus.drip m ∘ t:=funext fun i=>drip_tint ..
    have he : Lotus.tint (-x) ∘ Lotus.tint x ∘ u=u:= funext fun i=>Prod.ext (by simp) (by simp)
    rw [show ((Equiv.arrowCongr (Equiv.refl _) (Lotus.tint x)) u)=Lotus.tint x ∘ u from rfl,h]; unfold carries jetty; rw [he]
    have hp : e ∘ Lotus.drip m ∘ u=v ↔ Lotus.drip m ∘ u=e.symm ∘ v:=⟨fun l=>funext fun i=>by exact Eq.symm (e.symm_apply_eq.mpr ((congr_fun l i).symm)),fun l=>funext fun i=>by exact (congr_arg e (congr_fun l i)).trans (e.apply_symm_apply _)⟩
    rw [←hx]; by_cases he:e ∘ Lotus.drip m ∘ u=v
    · rw [if_pos he,if_pos (hp.1 he)]
    rw [if_neg he,if_neg (he ∘ hp.2)]
end YM.FormalBulk08.Kemp
