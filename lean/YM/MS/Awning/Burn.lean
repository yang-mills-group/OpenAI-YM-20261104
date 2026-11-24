import YM.MS.Awning.Cap
/-!
# External polynomial degrees. Finite value tests.
Linear constraints can be tested at any stage of Laurent/ODE construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Awning
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Signal Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{X:Type}{p h:ℤ}{m n:ℕ}{F H: Mob G}
variable {U:Rip G}{b:Bool}{k:ℂ}
lemma Ultra0 {H:Type}[NormedAddCommGroup H][NormedSpace ℝ H]: Ultra (0:Tree H ℂ):= fun j=> Costs.zero (fun _ p _=>div_nonneg (by simp) (by exact pow_nonneg ((Arc.path ..).weight_pos _ _).le _))
lemma core_sum (s: Finset X)(k:ℂ) (hk:k∈Town)(u:X→Tree E ℂ)(hu:∀ i∈s,Ultra (u i))(hr:∀ i∈s,Reflect (u i)) : coreC (cloud k) n (∑ i∈s,u i)= ∑ i∈s, coreC (cloud k) n (u i):= by
   classical
   induction s using Finset.induction with
   | empty=> simp_rw [ Finset.sum_empty ]; simpa only [zero_smul] using core_m (u:=(0:Tree E ℂ)) Ultra0 0 k n
   | insert i s hi ih=>
      have he (j:X)(hj:j∈s) := Finset.mem_insert_of_mem (b:=i) hj; rw [Finset.sum_insert hi,Finset.sum_insert hi, core_pl (hu i (by simp)) (hr i (by simp)) ( show Ultra (∑ j∈s,u j) from ?_ ) (show Reflect (∑ j∈s,u j) from ?_) hk, ih (fun j hj=>hu j (he j hj)) (fun j hj=> hr j (he j hj))]; swap -- he b/a ambiguity
      · intro x p; simp only [Finset.sum_apply]; exact Finset.sum_congr rfl (fun j hj=> hr j (he j hj) x p)
      convert! (tranquil s (z:=(0:UScale Unit)) (a:=1) (f:=fun i (_:Unit)=> u i) (fun j hj=> hu j (he j hj)) (fun _=> show 0≤(1:ℝ) from zero_le_one)) using 1; ext; simp
lemma carpet_alloc (hF:Form0 b F)(ht: Knot b U)(hQ: F∈ CapAir p G)(x v:E)(W:Touch G m E)(k:ℂ) : let L(i:ℝ):= sail W ( x+i • v ); let f(i:ℝ):= carpet (Px m) (Path.wing k U F ( ray ( L i ) ))
    ∀ t:ℝ, ∀ c:ℝ,(fun i:ℝ=> f i (t,c))∈ Bowl (PriceR p W):= by
   intro L f t c; apply (bowl_iff _).mpr; intro s μ hμ; unfold f carpet; simp_rw [← integral_const_mul]; rw [← integral_finsetSum _ (fun i _=> ?_) ]; swap; · exact ( (Q.Gmajor _ (exact_test hF.price ht.price (ray ( L i )) k) ()).values (t,c)).const_mul _ -- infer Tv
   have hv (r: SectorP m): ∑ i∈ s,μ i* Path.wing k U F (ray ( L i )) ((r,t),c) =0:= by
       apply hμ; let w:= Nat.le_succ m; let q:= Path.slideA (lt_add_one m) (r,t); convert! bowl_more ( price_M (h:=p) (Nat.le_succ m) W|>.le ) ( stockV hF ht hQ (c • x) (c • v) (move w W) q k) using 1
       ext; unfold Path.wing; simp_rw [ ← smul_comm c _ v, ← smul_add, L,ray_lift,lift_sail,Rock.moves]; rfl
   simp_rw [hv]; simp
lemma fuel (hF:Form0 b F)(hK: Knot b U)(hv:F∈ CapAir p G)(hk:k∈Town): ocean k U F∈ CapAir p G:= by
    intro m E _ _ _ W x v; let L(i:ℝ):= sail W (x+i • v); let f(i:ℝ):= carpet (Px m) (Path.wing k U F (ray (L i))); apply (bowl_iff _).mpr; intro s μ hμ; change ∑ i∈s,μ i * coreC (cloud k) m (f i) (1:ℝ)=0
    have h i:= carpet_test hF.price hK.price (ray (L i)) k; have hx i: Reflect (f i):= mirror_r (Px m) (wing_mirror hF.token hK.token k (ray (L i)))
    have ht: ∑ i∈s,μ i • f i=0:= funext (fun ⟨q,t⟩=>by rw [Finset.sum_apply]; exact hμ (fun i=> f i (q,t)) (carpet_alloc hF hK hv x v W k q t))
    have he:= core_sum (n:=m) s k hk (fun i=> μ i • f i) (fun i _=> Rapid.L (h i) ( ContinuousLinearMap.mul ℝ ℂ (μ i) )) (fun i _ q t=>by simp only [Pi.smul_apply,hx i q t])
    simp_rw [show ∀ i:ℝ, coreC (cloud k) m (μ i • f i) = μ i • coreC (cloud k) m (f i) from fun i=>core_m (h i) (μ i) k m] at he -- order ht rewrite
    rw [ht] at he; have hk0 : coreC (cloud k) m (0:Tree ℝ ℂ)=0:= by simpa only [zero_smul] using core_m (u:=(0:Tree ℝ ℂ)) Ultra0 0 k m
    rw [hk0] at he; simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congr_fun he.symm 1
lemma ignite {X:Flats G}{g r:ℤ} (hp: Dock.ClockD b g r X)(ht:SeedP (fun f=>To f ( CapAir p G )) X) : SeedP (fun f=> To f ( CapAir p G )) ( Dock.step0 G X ):= by
   refine (washed ( CapAir p G )).pipe _ _ _ (fun i=>?_); filter_upwards [sunny (Dock.clockMoon hp i),ht i,high0] with s hs ht hv; rw [swamp_spec (c_bo 0) hs hv]; exact ( CapAir p G ).smul_mem _ (fuel hs ( c_bo 0 ) ht hv)
end YM.MS.Awning
