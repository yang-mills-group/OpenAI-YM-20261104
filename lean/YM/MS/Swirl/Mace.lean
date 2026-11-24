import YM.MS.Swirl.Came
/-!
# Finite-rank Wick integration by parts and Euler scale Ward
No partition/Hafnian. Wick multiplication commutator then matrix identity to be verified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Cylinder Orbit Cog Orbit.LogReal Book Convolve Puff Actors
open scoped Topology ContDiff Interval
variable {I E A:Type}{p:Sector A}{F H:BL A}{n j k:ℕ}{h v:ℤ}{K L:Grain A}
variable [Fintype A] (x y:A)
abbrev Chill (K:Grain A)(a b:A):= 2*K a b
omit [Fintype A] in
lemma traceS (z w:A) (h: Cog.Sym p K): Chill K z w=cross (p z) (p w)* Chill K w z:= by unfold Chill; rw [h z w]; ring
abbrev TraceD (x:A)(K:Grain A): Op A ℂ:= ∑ j:A,Chill K x j • D j
local notation "Ψ"=> Orbit.Cog.frame K
local notation "ϱ"=> TraceD x K
local notation "aX"=> atLetter x
local infix:70 " ⋆ "=> product p
lemma heat_coin : Ψ aX=0:= by ext; simp [Orbit.Cog.frame,atLetter]
lemma heat_letter (he:Clear p K)(hv: Cog.Sym p K): Ψ ( aX ⋆ F ) = aX ⋆ ( Ψ F )+ ϱ F:= by
   classical
   have hee(j:A): Head p x j aX F = D j F := by unfold Head; rw [ hear, show Koszul.sign p (p j) (coin (A:=A) (1:ℂ))= _ from Eq.trans (Pure.signs (coin_pure (p:=p) 1) _) (by rw [cross_false',one_smul]),coin_product,one_smul ] -- implicit show wrong argument
   rw [Koszul.link_apply (b:=false) Ψ aX F, heat_coin, sign_id,map_zero,LinearMap.zero_apply,add_zero, add_comm]; congr 1; change Orbit.Cog.conn p K aX F = TraceD x K F; rw [pair_line he hv,TraceD, LinearMap.sum_apply,Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]; · exact Finset.sum_congr rfl fun i _=> congr_arg ((2*K x i) • ·) ( hee i )
   intro i hi he'; apply Finset.sum_eq_zero; intro j hj; unfold Head; rw [unheard _ he']; simp
lemma trdΩ : TraceD x L F=∑ i,Chill L x i • D i F:= by unfold TraceD; simp only [ LinearMap.sum_apply,LinearMap.smul_apply ]
lemma trace_κ (he:Clear p K)(hp:Symm p F): Ψ ( TraceD x L F )= TraceD x L ( Ψ F ):= by rw [trdΩ, trdΩ,map_sum]; simp_rw [ map_smul ]; exact Finset.sum_congr rfl fun i _=> congr_arg ( (Chill L x i) • · ) (brush K i he hp).symm
lemma select (he:Clear p K)(hv:Cog.Sym p K)(hp:Symm p F):(tep K (n+1)) ( aX ⋆ F )= aX ⋆ (tep K (n+1) F) + ϱ (tep K n F):= by
   induction n with
   | zero=> simp_rw [teen K,rise]; norm_num [ Module.End.one_apply, heat_letter x he hv ] -- brush binder check
   | succ n ih=>
        have ht : Ψ (tep K n F)=(n+1:ℂ) • tep K (n+1) F:= by rw [teen K,smul_inv_smul₀ ( Puff.Dynamics.zeroN' n )]
        rw [teen K (n:=n+1), ih, map_add,heat_letter x he hv, trace_κ x he ( te2 K hp ), ht, map_smul, teen K (n:=n+1), map_smul ]; rw [ smul_add,smul_add ]; rw [add_assoc]; congr 1; rw [ ← smul_add, inv_smul_eq_iff₀ (Puff.Dynamics.zeroN' (n+1)) ]; push_cast; module
omit [Fintype A] in
lemma letterN : Limit (atLetter x (R:=ℂ)) (1:ℕ):= fun l h=> by rcases l with _|⟨x,_|a⟩; simp at h; simp at h; rfl
lemma totalT (he:Clear p K)(hv:Cog.Sym p K)(hp:Symm p F): effect K (n+1) ( aX ⋆ F )= aX ⋆ ( effect K (n+1) F ) + ϱ ( effect K n F ):= by
   have hx (n:ℕ): effect K (n+1)=effect K n+ tep K (n+1):= Finset.sum_range_succ ..; induction n with
   | zero=> rw [hx]; simp_rw [LinearMap.add_apply,map_add]; rw [ select x he hv hp ]; simp [effect,rise]; abel
   | succ n ih=> rw [hx (n+1)]; simp_rw [LinearMap.add_apply]; rw [ih,select x he hv hp]; -- want RHS T₂ n+1 but binder
                  rw [map_add,hx n]; simp_rw [LinearMap.add_apply,map_add]; abel
lemma ibpV (he:Clear p K)(hv:Cog.Sym p K)(hp:Symm p F) (h:F∈ Mini A): View K ( aX ⋆ F ) = ∑ i:A, Chill K x i * View K (D i F):= by
   obtain ⟨n,hn⟩:= h; change Shot K _ []=_; rw [ dawn K ( n:=n+1 ) (by push_cast; rw [ add_comm (n:ℤ) ]; exact (letterN x).pair hn), totalT x he hv hp,Pi.add_apply, show ( aX ⋆ (effect K (n+1) F) ) []=0 from Eq.trans ( times_nil .. ) ( zero_mul _ ), zero_add,trdΩ,Finset.sum_apply ]; refine Finset.sum_congr rfl fun i _=>?_ ; change Chill K x i * D i _ []=Chill K x i * Shot K _ []; congr 1; rw [dawn K (Limit.up ( hn.tip i ) ( show (_:ℤ) ≤ n from (by omega) )) ]; unfold effect; -- preserving
   have hx := fun n:ℕ=> té_D K he hp ( n:=n ) i; simp_rw [LinearMap.sum_apply,map_sum,hx] -- simp may unfold tep power
end YM.MS.Swirl
