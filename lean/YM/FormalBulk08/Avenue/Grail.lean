import YM.FormalBulk08.Avenue.Plaza
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge
lemma press_core (G:Gauge)(hk:0<k)(hj:4≤j):∃ C:ℝ,0≤ C ∧ ∀ (v:Train j),(∀ n (x y:wire G n),‖bandR G v k n x y‖≤C) ∧ (∀ x y,‖bandP G v k x y‖≤ C):= by
   obtain ⟨C,hc,H⟩:=carnel_coat hk hj; have hh n (v:Train j) (x y: wire G n):‖bandR G v k n x y‖≤ C:= by rw [bandR_note]; split; exact H ..; exact (norm_zero.le.trans hc)
   exact ⟨C,hc,fun v=> ⟨fun n x y=> hh n v x y,fun x y=>le_of_tendsto' (lords G v hk hj x y).norm (fun n=>hh n v _ _)⟩⟩
lemma press_move (G: Gauge)(hk:0<k)(hj:4≤j) : ∃ C:ℝ,0≤ C ∧ ∀ (A: Levels G)(i N M:ℕ),A.clock.J i=j→i≤N→ N≤ M→ (∀ n:Side,∀ x y:wire G n, ‖bandR G (location A N i) k n x y-bandR G (location A M i) k n x y‖≤ C*fineR A N i) ∧ (∀ x y, ‖bandP G (location A N i) k x y-bandP G (location A M i) k x y‖ ≤ C*fineR A N i):= by
   obtain ⟨C,hc,H⟩:= coastD (G:=G) hk hj; refine ⟨C,hc,fun A i N M hp hn hm=>?_⟩; have he n (x y:wire G n): ‖bandR G (location A N i) k n x y-bandR G (location A M i) k n x y‖ ≤ C*fineR A N i:= by
       simp_rw [bandR_note]; split; exact H A i N M hp hn hm n _ _; rw [sub_self,norm_zero]; exact mul_nonneg hc (fineR_pos ..).le
   exact ⟨he,fun x y=>le_of_tendsto' (((lords G _ hk (hp ▸ hj) x y).sub (lords G _ hk (hp ▸ hj) x y)).norm) (fun n=>he n _ _)⟩
lemma kernel_color (v:Train j)(hk:0<k)(hj:4≤j): (kernelP G k v n)ᵀ=kernelP G k v n := by
   obtain ⟨η,B,ε,h,b,t,q,H⟩:= affiliates j hj k hk; obtain ⟨W,hw,H⟩:= H v; unfold kernelP; rw [← W.stands,Precision.K,←patron_star]; have hh:= (H n).symmetric.1; simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hh, Matrix.mul_assoc]
lemma rotor_gap (v:Train j)(hk:0<k)(p:Site n): rotor 1 k v (mon p) * buckle k v (mon p) * (symbol 1 (mon p))ᴴ = (symbol 1 (mon p))ᴴ:= by
    by_cases ht:p=0
    · subst p; simp only [mon_zero,buckle,↓reduceIte,Matrix.mul_zero,eq_self,Matrix.zero_mul];simp [Exterior.symbol, Exterior.q,wedge]
    have hp:=base_subset_realCube zone_pos (mon_mem n p);have he:=mon_peak p ht;rw [buckle,if_neg he,rotor_after 1 k hk v hp he,←signal_unit,←mirage_herm 1 (mon p) (real_frequency p) 1, Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,mirage_chain,Matrix.mul_zero,sub_zero]
lemma inverse_cross (v:Train j)(hk:0<k)(hj:4≤j): Precision.K ((pink k v).acts n)*carnel k v n*(d 1 n)ᵀ=(d 1 n)ᵀ:= by
    let R:= Precision.K ((pink k v).acts n); have he : approached R=spectral (fun p:Site n=> rotor 1 k v (mon p)):= by apply cancel_rotation n; rw [spectral_read]; exact runs_rotor k hk hj v n
    have hh:(d 1 n)ᵀ=realOf (spectral (fun p:Site n=> (symbol 1 (mon p))ᴴ)):= by rw [← spectral_adj,← d_spectral, realOf_adj]; ext i j; simp [approached,realOf]
    unfold carnel; rw [←realOf_mul, ← realOf_mul', he, prom_adj, d_spectral, spectral_adj,spectral_mul,spectral_mul]; simp_rw [rotor_gap v hk]; exact hh.symm
lemma invite (v:Train j)(hk:0<k)(hj:4≤j): kernelP G k v n * bandR G v k n *(Reef.force G n)ᵀ=(Reef.force G n)ᵀ:= by rw [kernelP,bandR, Reef.force,←patron_star,← patron_mul,← patron_mul, inverse_cross v hk hj]
lemma generalized (v:Train j)(hk:0<k)(hj:4≤j): kernelP G k v n * bandR G v k n*kernelP G k v n=kernelP G k v n:= by
   let V:= Reef.force G n; let M:=patron G ((pink k v).acts n)
   have he:kernelP G k v n=Vᵀ * M * V:= by unfold kernelP M V; rw [Precision.K, patron_mul,patron_mul,patron_star];rfl
   nth_rw 2 [he]; nth_rw 2 [he]
   rw [←Matrix.mul_assoc,←Matrix.mul_assoc]; exact congr_arg (fun p : Matrix (Lines G n 1) (Lines G n (1+1)) ℝ=>p*M*V) (invite (G:=G) v hk hj)
end YM.FormalBulk08.Avenue
