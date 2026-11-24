import YM.MS.Swirl.Cour
/-!
# Project both legs of Wick line. Green identity including pay. Orthogonal subset size matters.
 `Σ` desired inverse at all mesh arity (signal dressing).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Filter Set Finset Metric MeasureTheory Real
open Koszul Plane Orbit Cog Orbit.LogReal Book Convolve Program
open scoped Topology ContDiff Interval
variable {P:Type}{p:Sector P}[Fintype P]{K:Grain P} (S:Cog p){w:P→ℂ}{H:BL P}
local notation "f"=> Cog.mode S
local notation "ϕ"=> Cog.spin S
local notation "C"=> Chill K
local notation "Λ"=> S.Cascade K
set_option quotPrecheck false
lemma carry_G (ht:S.phase K)(v:Bool) (h: Green w K H)(hp:∀ i,w (f i)=w i): Green w (S.imageV v K) ( pay v • H ):= by
   cases v; · rw [show pay false=1 from rfl, one_smul ]; exact h
   let c:= S.Cascade K; refine ⟨ fun a b=>?_⟩
   have hl (x y:P): Chill c x y=C x y+C ( f x ) y*ϕ ( f x ):= by unfold Chill c Cascade; rw [Pi.add_apply,Pi.add_apply, mul_add,image_u ht, mul_assoc]; -- hp parentheses
   have hr(x y:P): Chill c x y=C x y+C x ( f y ) *ϕ ( f y ) := by unfold Chill c Cascade; rw [Pi.add_apply,Pi.add_apply,mul_add,imageW,mul_assoc]
   change (∑ i:P,∑ j:P,w i*Chill c a i*((pay true) • H) [i,j]* Chill c j b)=-w b*Chill c a b
   have hw(x y j:P): (∑ i:P, w i * C x i* ( pay true • H ) [i,j] * Chill c j y) = (∑ i:P,w i*C x i* H [i,j] * C j y)*((2:ℂ)⁻¹)+(∑ i:P,w i*C x i* H [i,j] * C j (f y))* ( (2:ℂ)⁻¹*ϕ (f y) ):= by
       rw [ Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun _ _=>?_ ; rw [hr]; simp only [Pi.smul_apply,smul_eq_mul,pay,if_true]; ring
   have hc (x y:P): (∑ i:P, ∑ j:P,w i * C x i*(pay true • H) [i,j]*Chill c j y) = (-w y * C x y)*((2:ℂ)⁻¹)+( -w ( f y )* C x ( f y ))*( (2:ℂ)⁻¹ *ϕ ( f y ) ):= by rw [ ← h.reads,← h.reads,Finset.sum_comm («f»:=fun i j=> w i * C x i*(pay true • H) [i,j]*Chill c j y) ]; simp_rw [ hw, Finset.sum_add_distrib, ← Finset.sum_mul ]; refine congr_arg₂ (·+·) (congr_arg ( · * _) ?_) (congr_arg ( · * _) ?_) <;> (simp_rw [Finset.sum_mul]; exact Finset.sum_comm)
   simp_rw [ show ∀ i j, w i*Chill c a i * ( pay true • H ) [i,j]*Chill c j b=w i * C a i * ( pay true • H ) [i,j] * Chill c j b + w i * C ( f a ) i * ( pay true • H ) [i,j] * Chill c j b*ϕ (f a) from fun i j=>by rw [hl a i]; ring, Finset.sum_add_distrib, ← Finset.sum_mul, hc ]; rw [hr a b,hp]; -- C fa b converted to image relation only with spins
   have hy : C ( f a ) b *ϕ ( f a )= C a ( f b )*ϕ ( f b ):= add_left_cancel ( ( hl a b ).symm.trans ( hr a b ) );
   unfold Chill at *; rw [ht a b];
   linear_combination (norm:=ring_nf) (w b)*( hy ) * (-(1/2:ℂ)) + - (w b)*( K a b )*( ( S.holo a ) ) - (w b)* ( K a b ) * (ϕ a *ϕ ( f a )) * S.holo b -- sign adjust from trace
namespace Near
open Landau Tone Frame Lattice City Detect Native Wilsonian
variable {G:Gauge}{n:Side}{b:Bool}
lemma planeS (u:Tag→ℂ): Green ( u∘ Eyes ) ( Master G n b ) ( pay b • flatH G n ) := carry_G (iota G n) ( riverOK BankK.pin BankK.gov ) b ( Θgreen u ) (fun _=> rfl)
-- team fees.Fr
abbrev inUse (p:Team)(x:ℝ)(i:FixedMode G n):= fieldV p x i.1
def pointV (t:Team)(x:ℝ)(i:Tag): Cn:= match i with
    | (false,u)=> adap t (some (0:Axis),u) x
    | (true,u)=> adap t (none,u) x
lemma rides (t:Team)(x:ℝ)(i:FixedMode G n): inUse t x i=pointV t x ( Eyes i ):= by rcases i with ⟨⟨⟨_|i,b⟩,j⟩,u⟩ <;> rfl
abbrev logD (V:Cn):= Eder V * (PowerSeries.invOfUnit V 1)
lemma DerM (V:Cn)(h:Low V): Eder V= logD V*V:= by unfold logD; rw [mul_assoc,PowerSeries.invOfUnit_mul V, mul_one ]; -- orientation; hv
                                                     rw [ ← PowerSeries.coeff_zero_eq_constantCoeff_apply, h ]; rfl
abbrev dust (G:Gauge)(n:Side)(p:Team)(x:ℝ): (FixedMode G n)→Cn:= fun i=> logD ( inUse p x i )
lemma feeDown (t:Team)(x:ℝ): ∀ i:FixedMode G n, Low (inUse t x i):= fun i=> adap0 t x i.1.1
lemma excavate (G:Gauge)(n:Side)(t:Team)(x:ℝ): Carrier (inUse t x) ( dust G n t x ):= fun i=> DerM _ ( feeDown t x i )
lemma guise (t:Team)(x:ℝ)(u:ℕ): Green ( Carrier.fees ( dust G n t x ) u ) (Master G n b) (pay b • flatH G n):= by
    have h: Carrier.fees ( dust G n t x ) u=(fun i:Tag=> PowerSeries.coeff u ( logD ( pointV t x i ) )) ∘ Eyes:= by funext i; unfold Carrier.fees dust Function.comp; rw [ rides ]
    rw [h]; exact planeS _
end Near
end YM.MS.Swirl
