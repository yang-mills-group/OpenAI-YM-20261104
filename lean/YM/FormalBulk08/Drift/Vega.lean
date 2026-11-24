import YM.FormalBulk08.Drift.Par
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I : Type} {G:Gauge}{η:ℝ}{σ:ℕ→ℝ}{K:KernelChoices}{E e r d D n:ℕ}{o:Loc G 1}
lemma marble_copy (l:ℕ)(n:Side){T:ℕ→ Anthem D G}{Y: Anthem D G}(h:∀ e≤ E,∀ r,Brass staticT o (fun _=>η) σ (fun _=>1) (fun i p=> T i p e r) (fun _ p=> Y p e r))(he:0≤η)(hp:Ends σ 0)(hx:∀ i,0≤σ i):
    let Q i p:= Kemp.banner l (T i p) n
    let L p:= Kemp.banner l (Y p) n
    ∀ e≤ E, (∀ p r, ∀ u:chain (wire G n) r, Ends (fun i=>marble r (coeff e (Q i p)) u) (marble r (coeff e (L p)) u)) ∧ (∀ p i,∀ r,l+e<r→ marble r (coeff e (Q i p))=0):= by
    intro Q L e he'; let V (T:Pot G)(k):=facade k (sieve n (T e k))
    have hv (T:Pot G) (r:ℕ): MvPolynomial.homogeneousComponent r (coeff e (Kemp.banner l T n)) = if r≤l+e then V T r else 0:= by
       unfold Kemp.banner; rw [coeff_mk,map_sum]; by_cases h : r≤ l+e
       · rw [if_pos h,Finset.sum_eq_single r]; refine MvPolynomial.homogeneousComponent_eq_self (facade_grade ..)
         intro k _ he; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade ..),if_neg]; omega
         simp [h]
       rw [if_neg h]; apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_range] at hi; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade ..),if_neg];omega
    have hV T r (h:l+e<r) : marble r (coeff e (Kemp.banner l T n))=0:=(marble_eq_zero_iff ..).mpr (by rw [hv,if_neg h.not_ge])
    refine ⟨fun p r u=>?_,fun p i=>hV (T i p)⟩; by_cases hz : r≤ l+e; swap
    · unfold Q L; simp_rw [hV _ r (lt_of_not_ge hz)]; exact tendsto_const_nhds
    have hW (T:Pot G): marble r (coeff e (Kemp.banner l T n))=sand (sieve n (T e r)) := by apply facade_unique (marble_agate _ _) (agate_sand _); rw [marble_grade,hv,if_pos hz,sand_facade]
    unfold Q L; simp_rw [hW,sand]; refine Tendsto.div_const (tendsto_finsetSum _ fun i _=>?_) _
    let k i:= sieve n (T i p e r);let q:= sieve n (Y p e r);let v:= u -- need i
    let x:=u ∘ i
    obtain ⟨⟨B,b,w,W⟩,⟨C,c,u,U⟩,A,a,s,V⟩:= h e he' r; have H : Faint staticT σ (fun i=> k i x-q x):= by
       refine ⟨_, a.times (soft_coin _ ‖p‖),fun i=>mul_nonneg (s i) (norm_nonneg _),fun i=>?_⟩; have ht': k i-q=sieve n (T i p e r-Y p e r):= ((sieve_sub_add n ((penn_total (W i p) he).of_norm) ((penn_total (U i p) he).of_norm)).2).symm
       have hb:= cool (sieve_bill n _ _ he (V i p)) he x; exact le_trans (le_of_eq (congr_arg abs (congr_fun ht' x))) (hb.trans_eq (by ring))
    change Ends (fun i=> k i x) (q x); convert (quietude hp hx H).add_const (q x) using 1; · ext1 j; exact (sub_add_cancel ..).symm
    rw [zero_add]
end YM.FormalBulk08.Drift
