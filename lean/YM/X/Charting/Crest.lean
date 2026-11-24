import YM.X.Charting.Eyes
/-!
Uniform outgoing far bounds grouped by fixed polynomial. Restores all tadpole contributions (none) by `budget_triple`. Mandatory joint with F fields at prescribed sites.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "K"=> (atTop:Filter ℕ)
variable {α β V:Type*}
set_option quotPrecheck false
variable (d:ℕ)(hd:0<d)(p : PlaqAxes) (a:Bool)(o z x:Beam q) {i j:Hair G}
variable (A B :(k:ℕ)→Jam (side q k) G)
local notation:max "F" i:max => (moon d p a o i (z i))

def live (a:Bool):Symmetric (Jam n G):= if a then water else sale
lemma colors_only (a:Bool) (i j:Jam n G)(h : i.2≠j.2): (live a).cov i j=0:= by cases a <;> (first|rfl| simp only [live,↓reduceIte,Bool.false_eq_true])
                                                                               · simp [sale,dev,Ne.symm h]
                                                                               rw [water_dev];simp [dev,east,reverseK, Ne.symm h]
include hq
lemma lead_sale (h:∀ᶠ k in K,F k≤4*mass (A k).1.1 (B k).1.1) : Ripe q (fun k=> ((F k^2:ℝ):ℂ)*sale.cov (A k) (B k)) 0:= by
   obtain ⟨C,hC,H⟩:= typical hq; refine Ripe.costed (a:=16*C) ?_; filter_upwards [h,H] with k hk h; rw [norm_mul]; unfold sale dev; simp only [Complex.norm_real]; split
   next=>
      let u:= (B k).1.1; let v:= (A k).1.1; rw [Real.norm_of_nonneg (sq_nonneg (F k))]; let q:=mass v u; have hR : q = (1:ℝ)+pdist (u-v):= by unfold q; rw [mass_eq, ← pdist_neg (u-v), neg_sub] -- maybe let?
      refine (mul_le_mul_of_nonneg_left (h (u-v)) (sq_nonneg _)).trans ?_; rw [← hR, ← mul_div_assoc]; apply (div_le_iff₀ (pow_pos (zero_lt_one.trans_le (mass_pos ..)) _)).mpr; change F k≤4*q at hk; nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (moon_pos p o a k d _)) hk 2) hC.le]
   rw [norm_zero, mul_zero]; positivity
lemma buoy : Ripe q (fun k=> (live a).cov (A k) (B k)) 0:= by
   cases a; exact bounded_sells hq _ _
   simp_rw [live,if_true,water_dev, Complex.ofReal_sub]; exact IsBigO.sub (f₁:=fun k=> sale.cov (A k) (B k)) (f₂:=fun k=> sale.cov (reverseK (A k)) (B k)) (bounded_sells hq _ _) (bounded_sells hq _ _)
include hd
lemma lead_live (h:Capt d o x) (i j:Hair G): Ripe q (fun k=> ((F k^2:ℝ):ℂ)*thermal (live a) (z k) (x k) j i) 0:= by
   let J (k:ℕ) := place (z k) j; let A(k:ℕ):= place (x k) i
   have he (a:Bool): Ripe q (fun k=> ((moon d p a o k (z k)^2:ℝ):ℂ) * sale.cov (J k) (A k)) 0:= lead_sale hq d p a o z J A (near_eye_bound hq p a o z x i z (fun k=>(J k).1.1) _ (fun k=>place_near ..) (fun k=>minmass₀ ..) d hd h) -- var i in binder order implicit
   cases a; exact he _
   let Q(k):=reverseK (J k); let Z:Beam q:= fun k=> second p (z k); simp_rw [live,if_true,thermal,water_dev,Complex.ofReal_sub,mul_sub]
   apply (he true).sub (f₂ := fun k=>_ * sale.cov (Q k) (A k)) -- edit: f implicit unknown
   apply lead_sale hq d p true o z Q A (near_eye_bound hq p true o z x i Z _ (rounds (step p.val.1+step p.val.2-j.1.1-step j.1.2)) ?_ (fun k=> min_le_right ..) d hd h); intro k; unfold Q J; rw [reversePlace,separation_comm, separation,show second p (z k)=Z k from rfl, add_sub_cancel_right]; apply round_fee

omit hd hq
variable (O:α→Site n) (U:α→Beam q)
local notation "Sum'"=> ((α×Hair G) ⊕ Hair G)
def stageAt (O:α→Site n)(y:α×Hair G):Jam n G:= place (O y.1) y.2
def alignment (O:α→Site n)(y:Site n) (P:Symmetric (Jam n G)):= remap (Sum.elim (stageAt O) (place y)) P
lemma align (K' :Symmetric (Jam n G))(P:poly (α×Hair G))(Q:Curly G)(u:Site n): shock (alignment O u K') (co P*coda Q)= shock K' (hairAt u Q*(rename (stageAt O) P)):= by rw [alignment, remaps,map_mul,mul_comm]; unfold coda co; rw [rename_rename,rename_rename];rfl

def fees (K' :Symmetric (Jam n G)) (P:poly (α×Hair G))(v: Curly G)(u:Site n):= shock K' (hairAt u v* (rename (stageAt O) P))
variable (P:poly (α×Hair G))
include hq hd
lemma highfees (H:∀ i:α,Capt d o (U i))(z:Beam q): Ripe q (fun k=> ((moon d p a o k (z k):ℂ)^6)* fees (fun i=> U i k) (live a) P (vertex p) (z k)) 0:= by -- signature
   let M(k:ℕ):= alignment (fun i=> U i k) (z k) (live (G:=G) a)
   simp_rw [fees,← align (fun i=>U i _)]; apply Eq.mp ?_ (budget_triple (q:=q) P M (fun i=> Complex.ofReal (moon d p a o i (z i)^2)) (vertex_triples p) ?_ ?_ ?_)
   · congr 1; funext k; push_cast; ring -- M unfolds?
   · intro k i j h; simp_rw [M,alignment,remap_cov,Sum.elim_inr]; exact colors_only a _ _ h
   · intro i j; simp_rw [M,alignment,remap_cov,Sum.elim_inl]; exact buoy hq _ _ _
   intro i j; simp_rw [M,alignment,remap_cov,Sum.elim_inl,Sum.elim_inr]; exact lead_live hq d hd p a o z (U j.1) (H j.1) j.2 i

lemma whole (H:∀ i:α,Capt d o (U i)) : ∃ c> (0:ℝ),∀ᶠ k in K,∀ z:Native q k,(moon d p a o k z)^6*‖fees (fun i=> U i k) (live a) P (vertex p) z‖≤ c:= by
   let f (k:ℕ)(z:Native q k):= (moon d p a o k z)^6*‖fees (fun i=> U i k) (live a) P (vertex p) z‖; choose z hz h using fun k=> Finset.exists_max_image Finset.univ (f k) Finset.univ_nonempty
   obtain ⟨c,hc,H⟩:= (highfees hq d hd p a o U P H z).exists_pos; refine ⟨c,hc, H.bound.mono fun k hk z'=> (h k z' (Finset.mem_univ _)).trans ?_⟩; unfold f; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (moon_pos p o a k d _)),tickets_zero,norm_one,mul_one] at hk; exact hk
end YM.PositionX.Hinge
