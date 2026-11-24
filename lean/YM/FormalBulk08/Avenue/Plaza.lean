import YM.FormalBulk08.Avenue.Peak
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
lemma glimpsed (v:Train j)(hk:0<k)(hj:4≤j)(a b x): IntegrableOn (stall k v x a b) (ball 0 Real.pi) := by obtain ⟨C,h,H⟩:=stall_prices hk hj; exact (rock_lim (vacancy ..) (welcome k hj v a b x) C h.le (fun n i hi=> H v a b n x i hi)).1
lemma glimpse (v:Train j)(hk:0<k)(hj:4≤j)(a b x y): Tendsto (fun n:Side=> carnel k v n (wrap n x,a) (wrap n y,b)) atTop (𝓝 (reins k v (x-y) a b)) := by
   obtain ⟨C,h,H⟩:=stall_prices hk hj
   simp_rw [canon_rate]; exact ((rock_lim (vacancy ..) (welcome k hj v a b _) C h.le (fun n i hi=> H v a b n _ i hi)).2).const_mul _
lemma stall_empty (v:Train j)(x:Cover)(a b:TypeFace 1): stall k v x a b (tone n (Lattice.lift (0:Site n)))=0:= by rw [show tone n (Lattice.lift (0:Site n))=0 from funext fun i=>by simp [tone,lift_origin n]]; exact vacancy ..
lemma bigness:0≤∫ x:Pitch,province x:= integral_nonneg province_pos -- remove binder
lemma carnel_coat (hk:0<k)(hj:4≤j):∃ C:ℝ,0≤C∧∀ (n:Side)(v:Train j) a b, ‖carnel k v n a b‖ ≤ C:= by
    obtain ⟨C,h,H⟩:=stall_prices hk hj
    refine ⟨titular*(C*∫ x:Pitch,province x), mul_nonneg titular_p.le (mul_nonneg h.le bigness),?_⟩
    rintro n v ⟨x,a⟩ ⟨y,b⟩; rw [← Lattice.wrap_lift x,← Lattice.wrap_lift y,canon_rate,norm_mul,Real.norm_of_nonneg titular_p.le]; apply mul_le_mul_of_nonneg_left _ titular_p.le
    exact rock_price C _ (fun i hi=> H v a b n _ i hi) h.le (stall_empty v _ _ _)
lemma vest (hk:0<k)(hj:4≤j) : ∃ C:ℝ,0<C ∧ ∀ (A:Levels G)(i N N':ℕ), A.clock.J i=j→i≤N→ N≤N'→ ∀ (n:Side) (x:Cover)(p:Site n) a b,p≠0 → ‖stall k (location A N i) x a b (tone n (Lattice.lift p))-stall k (location A N' i) x a b (tone n (Lattice.lift p))‖ ≤ C*fineR A N i/‖tone n (Lattice.lift p)‖^2:= by
   obtain ⟨C,h,H⟩:=levelD_rate (G:=G) _ hj k hk; refine ⟨C,h,fun V j a b he ht hv n x p s t hp=>?_⟩
   let y:=mon p; have hy:y≠0:=mon_peak p hp
   rw [stall,stall,tone_maps, buckle,buckle,if_neg hy,if_neg hy,←mon_size]; rw [←Complex.sub_re,Real.norm_eq_abs, ←mul_sub]; apply le_trans (Complex.abs_re_le_norm _); rw [norm_mul,mode_real _ _ (real_frequency p),one_mul]
   simp_rw [fieldD, mask_value];by_cases hr:s=t;rw [if_pos hr,if_pos hr,scaleD_one,scaleD_one]; exact H _ _ a b (mon p) (axisEquiv.symm s) he (mon_mem n p) hy ht hv
   rw [if_neg hr,if_neg hr,sub_self,norm_zero]; have hm:=fineR_pos V a j; positivity
lemma coastD (hk:0<k)(hj:4≤ j): ∃ C:ℝ,0≤C∧∀ (A: Levels G)(i N N':ℕ),A.clock.J i=j→i≤N→ N≤N'→∀ (n:Side) a b,
    ‖carnel k (location A N i) n a b-carnel k (location A N' i) n a b‖ ≤ C*fineR A N i := by
   -- vest independent of torus side! signature revise
   obtain ⟨C,h,H⟩:=vest (G:=G) hk hj; let D:=∫ x:Pitch,province x
   refine ⟨titular*(C*D),mul_nonneg titular_p.le (mul_nonneg h.le bigness),?_⟩
   rintro A i N N' hn hv he n ⟨x,a⟩ ⟨y,b⟩; let p:= Lattice.lift x; let q:= Lattice.lift y; rw [← Lattice.wrap_lift x, ←Lattice.wrap_lift y,canon_rate,canon_rate,←mul_sub, ←smul_sub, ←Finset.sum_sub_distrib,norm_mul, Real.norm_of_nonneg titular_p.le]
   apply (mul_le_mul_of_nonneg_left (rock_price (C*fineR A N i) _ (fun z hz=> H _ _ _ _ hn hv he n (p-q) _ a b hz) (mul_nonneg h.le (fineR_pos ..).le) (by rw [stall_empty,stall_empty,sub_zero])) titular_p.le).trans_eq; unfold D; ring
-- © covers. color extension
open Reef Lotus Shore Mesa City Gorge
variable (G)
def bandP (v:Train j)(k:ℝ)(x y:edgeL G):ℝ := if x.2.2=y.2.2 then reins k v (x.1-y.1) x.2.1 y.2.1 else 0
def bandR (v:Train j)(k:ℝ)(n:Side) := patron G (carnel k v n)
set_option maxHeartbeats 600000 in
lemma blue_cost (Q : Matrix (Body 1 n) (Body 1 n) ℝ) (x y:wire G n) : patron G Q x y=if x.2.2=y.2.2 then Q (x.1,x.2.1) (y.1,y.2.1) else 0 := by
    let z:wire G n→ℝ:=Pi.single y (1:ℝ); have hp: patron G Q x y=(patron G Q *ᵥ z) x := (congr_fun (Matrix.mulVec_single_one (patron G Q) y) x).symm; rw [hp]
    have he: atPaint z x.2.2= if x.2.2=y.2.2 then Pi.single (y.1,y.2.1) 1 else 0:= by
        funext p; by_cases hh:x.2.2=y.2.2
        · rw [if_pos hh]; change z (_,_,x.2.2) = _;rw [hh] ; unfold z; obtain ⟨u,a,b⟩:=y; obtain ⟨j,v⟩:=p; simp only [Pi.single_apply,Prod.mk.injEq,eq_self,and_true]
        rw [if_neg hh]; change z (_,_,_)=(0:ℝ); apply Pi.single_eq_of_ne; exact fun e=>hh (congr_arg (a₁:= (p.1,p.2,x.2.2)) (fun p:wire G n=>p.2.2) e)

    rw [show (patron G Q *ᵥ z) x=(Q*ᵥ atPaint z x.2.2) (x.1,x.2.1) from congr_fun (paint_eats Q z x.2.2) (x.1,x.2.1),he];split;rw [Matrix.mulVec_single_one];rfl
    rw [Matrix.mulVec_zero];rfl
lemma bandR_note (v:Train j)(k:ℝ)(n:Side) (x y:wire G n) : bandR G v k n x y=if x.2.2=y.2.2 then carnel k v n (x.1,x.2.1) (y.1,y.2.1) else 0 :=blue_cost G _ _ _
lemma lords (v:Train j)(hk:0<k)(hj:4≤j)(x y:edgeL G): Tendsto (fun n:Side=>bandR G v k n (Lotus.drip n x) (Lotus.drip n y)) atTop (𝓝 (bandP G v k x y)):= by
   simp_rw [bandR_note,bandP]; split
   next hp=> refine (glimpse v hk hj x.2.1 y.2.1 x.1 y.1).congr ?_; intro n;simp [Lotus.drip ,hp]
   next hp=> apply tendsto_const_nhds.congr; intro n; simp [Lotus.drip ,hp]
end YM.FormalBulk08.Avenue
