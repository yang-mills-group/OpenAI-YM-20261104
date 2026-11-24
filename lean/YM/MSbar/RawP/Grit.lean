import YM.MSbar.Aqua.Seine
import YM.MSbar.Chord.Sensor
import YM.Push.STATIONARY_UNIFORM.Support
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open AnalyticBridge.SectorAffine.Offset
variable {G:Gauge}{n:Side}{σ E ι:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype σ]
variable {C K D a w:ℝ}{p k:ℕ}{l:σ→Site n}{y:Site n} {x: Positions σ}{f : Positions σ→E}
lemma riseA (h:Through k f x C)(he:Requests Set.univ f l y p)(ha:0≤a): Beacon l a k f y x (C*Real.exp (a*(k*p:ℕ))) :=by
  intro j hk q; by_cases hs : ∀ i,separation y (l (q i)) ≤ p
  · have hz : spanSites l y q≤ k*p := (Finset.sum_le_sum (g:=fun _ => p) (fun i _ => hs i)).trans (by simp [Nat.mul_le_mul_right p hk]); rw [mul_assoc,← Real.exp_add]; refine ((entry_bound q).trans (h.pay _ hk)).trans (le_mul_of_one_le_right h.nonneg (Real.one_le_exp ?_)); linarith only [mul_le_mul_of_nonneg_left (show (spanSites l y q:ℝ) ≤ (k*p:ℕ) by exact_mod_cast hz) ha]
  push Not at hs; obtain ⟨i,hi⟩:= hs; rw [he.zero Filter.univ_mem (h.smooth.of_le (Nat.cast_le.mpr hk)) _ _ (Nat.not_le.mpr hi), norm_zero]; exact mul_nonneg (mul_nonneg h.nonneg (Real.exp_pos _).le) (Real.exp_pos _|>.le)
variable {s:Set (Positions σ)} (g:ι→Positions σ→E)(t v:ι→ℝ) (hh: IsOpen s)(hn:Convex ℝ s)(hg: ∀ i x,x∈s → Through k (g i) x (t i)) (hx:x∈s)(ht:Summable t)(hv:Summable v)(hp:∀ i:ι,Beacon l a k (g i) y x (v i))
include hg hh hn ht hx hp hv
lemma cargo [CompleteSpace E] : Beacon l a k (fun x=>∑' i,g i x) y x (∑' i,v i) :=by
   intro k' he q
   let T:= ContinuousMultilinearMap.apply ℝ (fun _:Fin k' =>Positions σ) E (fun i=> Uniform.bolt (q i)); let W(z):= ∑' i,g i z
   have hz:= T.hasSum (Midpoint.will hh hn hg ht he x hx); let u(i:ι):= Uniform.entry (g i) x q
   change HasSum u (Uniform.entry W x q) at hz; let c:= Real.exp (-a*spanSites l y q); have he' : Summable (fun i=> v i*c):=hv.mul_right _; have hh': Summable (fun i=> ‖u i‖):= he'.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> hp i k' he q); change ‖Uniform.entry W _ q‖ ≤ _; rw [←hz.tsum_eq, ← tsum_mul_right]; exact (norm_tsum_le_tsum_norm hh').trans (hh'.tsum_le_tsum (fun i=>hp i k' he q) he')
omit hg hh hn ht hx hp hv
section native
variable (b:y∈(univ : Finset (Site n))) -- unused
lemma dimr (l:σ→Site n)(v : List σ)(x:Site n): Whisk.extent (Whisk.zone l ∅ v) ≤ 2*spanSites l x v.get:=by
     have he(i:Site n)(hi:i∈Whisk.zone l ∅ v): separation x i ≤ spanSites l x v.get:=by rw [Whisk.zone,empty_union,List.mem_toFinset] at hi; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hi; obtain ⟨y,rfl⟩:=List.get_of_mem hb; exact single_le_sum (s:=Finset.univ) (f:=fun j:Fin v.length=> separation x (l (v.get j))) (fun _ _=> Nat.zero_le _) (mem_univ y) -- y
     refine Whisk.yard fun i hi j hj=> (separation_triangle i x j).trans ((Nat.add_le_add ((separation_comm ..).trans_le (he i hi)) (he _ hj)).trans_eq (by omega))
noncomputable def raiseQ (l:σ→Site n)(a:ℝ)(T:List σ) := Real.exp (-a*Whisk.extent (Whisk.zone l ∅ T))
local notation "ℓ"=> raiseQ l a
lemma ropeCost (b:σ)(L:List σ)(ha:0≤a) : Real.exp (-(3*a)*spanSites l y ((b::L).get)) ≤ Decay a (l b) y * raiseQ l a (b::L):=by
    let X:= b::L; unfold Decay raiseQ; rw [separation_comm (l b),← Real.exp_add]; apply Real.exp_monotone; have he':separation y (l b) ≤ spanSites l y X.get:= by apply le_trans _ (Finset.single_le_sum (f:=fun j:Fin X.length=> separation y (l (X.get j))) (fun _ _=> Nat.zero_le _) (a:=⟨0,Nat.pos_of_ne_zero (by unfold X;simp)⟩) (Finset.mem_univ _)); rfl
    have ht: Whisk.extent (Whisk.zone l ∅ X)+separation y (l b) ≤ 3*spanSites l y X.get:=by have hh:=dimr l X y; omega
    linarith only [mul_le_mul_of_nonneg_left (show (Whisk.extent (Whisk.zone l ∅ X):ℝ)+separation y (l b) ≤ 3*spanSites l y X.get from (by exact_mod_cast ht)) ha]
lemma fEntry (he : ContDiffAt ℝ k f x)(q:List σ)(hk:q.length≤k): roc f (q.map Uniform.bolt) x=Uniform.entry f x q.get:=by
   let L:= q.map (@Uniform.bolt σ); have ht:L.length=q.length:= by unfold L; rw [List.length_map]
   rw [show roc f _ _=_ from rod k L _ he (by omega)]; unfold entry
   -- change cardinal via Eq.rec
   have hz (m n:ℕ)(hh:m=n)(Z:Fin m→Positions σ)(u:Fin n→Positions σ)(he: Z=u ∘ Fin.cast hh): iteratedFDeriv ℝ m f x Z=iteratedFDeriv ℝ n f x u:=by subst n; congr 1
   apply hz _ _ ht; funext i; simp [L]
end native
end YM.MSbar.RawP
