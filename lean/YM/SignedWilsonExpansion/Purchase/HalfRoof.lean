import YM.SignedWilsonExpansion.F9.CenterWarp
import YM.SignedWilsonExpansion.Purchase.MathFrame
import YM.FVA2.Speed.Firm
/-! # Auxiliary mesh arrangement and cell embedding. Index/count derivation paid on actual aperture.
 We do not require top mesh arising from fixed quadratiol `step n`. Cost `ɛ` read on arbitrary Stretched.
 Address orientation = `3` bottom.Volume retained, no periodic cache sharing across cutters.
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV.Mer.Xa UVClock Schedules
open XSpace XSpace.Cirrus XSpace.Expense
open scoped Topology Classical BigOperators
variable {G:Gauge} {M: Levels G}{e k i j:ℕ}{ι:Type*}
def gainB (A:Schedule) (l:ℕ) (d:ℕ): ℕ:= ∏ a∈ Finset.range d,( A.block ( l+a)).val
abbrev parcel (A:Schedule)(l c:ℕ): ℕ:= gainB A l (c-l)
lemma gain_pos (A:Schedule)(l d): 0<gainB A l d:=Finset.prod_pos fun i _=> ( A.block _ ).pos
lemma gain_step (A:Schedule)(l d): gainB A l (d+1)=gainB A l d*(A.block (l+d)).val:= Finset.prod_range_succ ..
lemma parcel_next (A:Schedule)(p:i≤j): parcel A i (j+1)=parcel A i j * (A.block j).val:=by rw [parcel, show j+1-i=j-i+1 by omega,gain_step,Nat.add_sub_of_le p]
lemma line_step (A:Schedule)(l d): (gainB A l d:ℝ)*A.a (l+d)= A.a l:=by
    induction d with | zero=> simp [gainB] | succ d h=> rw [gain_step,Nat.cast_mul, ←Nat.add_assoc, A.a_step (l+d),mul_assoc,mul_div_cancel₀ (A.a (l+d)) ( by positivity : ( (A.block ( l+d)).val:ℝ)≠ 0),h ] -- lemma wrong order
lemma parcel_size (A:Schedule)(p:i≤j): (parcel A i j:ℝ)*A.a j=A.a i:=by simpa [ Nat.add_sub_of_le p ] using (line_step A i (j-i))
local notation "S"=> M.S
abbrev finalP : Period:= ⟨⟨16,by decide⟩,by decide,by decide⟩
def orbitP (A:Schedule)(l c:ℕ): Period := let L:=parcel A l c; let p:= gain_pos A l (c-l); ⟨⟨16*L,mul_pos (by decide) p⟩, dvd_mul_of_dvd_left (by decide) _, (show 4≤16 by decide).trans (Nat.le_mul_of_pos_right _ p)⟩
def roof (A:Levels G)(l c:ℕ)(σ:ℝ)(p:0<σ): Mesh := ⟨orbitP A.S l c,sizeT A σ c,sizeT_pos _ p _⟩
lemma orbit_vol {σ:ℝ}(h:0<σ)(p:i≤j): (roof M i j σ h).size= 16*sizeT M σ i:=by
   change _= 16*(M.S.a i/ σ); rw [← parcel_size S p]; change (M.S.a j/σ)*(( 16*parcel S i j:ℕ):ℝ)= _; push_cast; ring
def summit (A:Levels G)(l c:ℕ): Cover:= (parcel A.S l c) • ( fun _:Axis=> (3:ℤ) )
lemma elements (A:Levels G)(l c:ℕ)(i:Axis) : ( summit A l c i:ℝ)= (parcel A.S l c:ℝ)*3:= by unfold summit; simp [Pi.smul_apply]
lemma senior (A:Levels G) {l c:ℕ}: Center A l c (summit A l):= ⟨fun i p h=> by rw [summit,parcel_next _ p,mul_comm _,mul_smul]; rfl ⟩
def lumber (F:Mesh): Four ℝ:= fun i=>3/16*F.size
lemma position (F:Mesh) : lumber F ∈ F.Box:=by have hp:=F.size_pos; exact ⟨fun i=> by change F.size/8 ≤ 3/16*F.size; linarith, fun i=> by change 3/16*F.size≤ F.size/4; linarith⟩ -- wrong change
lemma summit_size {σ:ℝ}(v:0<σ)(p:i≤j) (a:Axis): let U:= roof M i j σ v; U.spacing * (summit M i j a:ℝ)=(lumber U) a:=by
    intro F; rw [elements,lumber,Mesh.size]; change _= (3/16)*(F.spacing*((16*parcel S i j:ℕ):ℝ)); push_cast; ring
-- Stretched and shopping.Once.F.Bool.Cap
section
variable {ρ B:ι→ℝ}{L:Filter ι}(z: Rise B L)(v:∀ i,0<ρ i) (l c:ι→ℕ)
local notation "S₁"=> (fun i=>roof M (l i) (c i) (ρ i) (v i))
variable (hc: l ≤ᶠ[L] c) (he: Eclipse L B (hereD M ρ l))(ht:Tendsto (hereD M ρ c) L (𝓝 0)) (hw: ∃ k'>0,payD B (-k')≤ᶠ[L] hereD M ρ c)
include z hc v he ht hw
lemma sideCosts : Eclipse L B (fun i=> sides S₁ i):=by
    have hv:(hereD M ρ l) ≤ᶠ[L] (fun i=> sides S₁ i):=by
       filter_upwards [ht.eventually_le_const zero_lt_one,hc] with i hi hp
       let U:= S₁ i; have hx:(U.spacing* U.p.side.val)= 16* hereD M ρ l i:= orbit_vol ( v i ) hp; have hu: U.spacing ≤1:= hi
       exact le_trans (b:=16*hereD M ρ l i) (le_mul_of_one_le_left (sizeT_pos _ ( v i ) _).le (by norm_num)) (hx.symm.trans_le (mul_le_of_le_one_left (Nat.cast_nonneg _) hu))
    exact ⟨fun x=>(he.tall x).trans hv⟩
lemma purchased_top : Stretched L S₁:=by
    have ht':Eclipse L B (sides S₁):= sideCosts z v l c hc he ht hw
    refine ⟨ht,fun k=>?_⟩; rcases hw with ⟨e,z',hh⟩; apply tendsto_atTop_mono' _ (?_) (payD_looms z zero_lt_one); filter_upwards [hh, ht'.tall ( 1+k*e ) ] with i hi hv
    have he:payD B 1 i= payD B (-e) i^k* payD B ( 1+k*e ) i:= by nth_rw 1 [show (1:ℝ)= k*(-e)+(1+k*e) from by ring]; rw [payD_add,payD_pow]; rfl
    rw [he]; exact mul_le_mul (pow_le_pow_left₀ (pay_pos ..|>.le) hi _) hv (pay_pos ..|>.le) (pow_nonneg (Expense.actual S₁ i).le _)
lemma reserve_space (n:ℕ): ∀ᶠ i in L, n< (S₁ i).p.side.val:= by
    have hp: Tendsto (sides S₁) L atTop:= ( purchased_top z v l c hc he ht hw ).horizon; filter_upwards [hp.eventually_gt_atTop ( n:ℝ)] with i hi using Nat.cast_lt.mp hi
end
-- lift by absolute lower count
variable {l m n c:ℕ}
def pine (A:Schedule)(l c:ℕ)(x: Fin n→ Cover):Fin n→Cover:= (parcel A l c) • x
lemma pine_home (A:Schedule) (x:Fin n→Cover): pine A l l x=x:=by unfold pine parcel gainB; simp
lemma pine_next (x:Fin n→Cover) (p:l≤ i): pine S l (i+1) x=fun j=> childFrom M i (pine S l i x j):=by rw [pine,parcel_next _ p,mul_comm _,mul_smul]; rfl
lemma stampL (A:Schedule) {m l:ℕ}(x:Fin n→ Cover)(i:Fin n)(j:Axis): ( pine A m l x i j:ℝ)= (parcel A m l:ℝ)*( x i j:ℝ):=by unfold pine; simp [Pi.smul_apply]
lemma stamp_pine (x:Fin n→Cover)(t:ℝ)(ht:0<t)(p:m≤ i): Extraction.tag (sizeT M t i) (pine S m i x)= Extraction.tag (sizeT M t m) x:=by
    apply PiLp.ext; intro j; apply PiLp.ext; intro a; change _ * (pine S m i x j a:ℝ)=_*_; rw [stampL]; unfold sizeT; rw [← parcel_size S p]; ring
-- e.g. TOM at x-axis
abbrev portrait (A:Levels G)(l c:ℕ)(σ:ℝ)(v:0<σ)(x:Fin n→ Cover) : Sample n:= ⟨roof A l c σ v,(fun i=> summit A l c+x i), lumber (roof A l c σ v) ⟩
lemma stillShot (x:Fin n→Cover)(t:ℝ)(u:0<t)(p:l≤ c): familiar (portrait M l c t u x)=Extraction.tag (sizeT M t c) x:=by
    apply PiLp.ext; intro j; apply PiLp.ext; intro a; let F:= roof M l c t u; change F.spacing * ( (( (summit M l c+x j) a):ℤ):ℝ) - lumber F a= F.spacing*(x j a:ℝ); rw [Pi.add_apply,Int.cast_add, ← summit_size u p _]; ring
end YM.SignedWilsonExpansion.Purchases.HalfRoof
