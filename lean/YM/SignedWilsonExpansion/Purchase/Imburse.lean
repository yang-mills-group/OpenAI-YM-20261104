import YM.SignedWilsonExpansion.Purchase.FacetClock
/-!
# Pricing itinerary.Concrete.Fix clothes.S.
At epochs ℓ many requirements.EnD.ReCoupon.* Charged little-o transport.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense Ticket Cosmos Cosmos.Polestar Source
open MarqueQ Method PorchK Epic Stair FVA2 FVA2.Scale
open scoped Topology Classical BigOperators
variable {G:Gauge}{M:Levels G}{e n h d k u K:ℕ}{ι:Type}{J:Type*} {T:Initialize G} {R:Realm G (e+1) Credit.leanC}{F:Labels.Frames G}{Ω:Council F}
open WardBin
variable {B Y A U ρ X Y' H:ι→ℝ} {l m c b v r w P':ι→ℕ}{L:Filter ι}
variable (p:∀ i,0<ρ i)(Q:∀ h,Rays G h T.hol) (Z:ι→ PorchK T F Q Ω R h k u) (H':Yonder Q R L m b v c r l U p Z B) {E β Γ:ℝ}
-- Pay market [eclipse born, vC<H.Size].[Partner.Growing via (24) horizon demand prepaid uniformly after staffing].
lemma spendMark {x:ℝ}(w:Rise B L)(p:Consume B L E U)(z:E < x): ∀ n:ℕ, ((dollar B)^n*U)=o[L] (payD B x):=by
    intro n; let t:= x-E; have ht:0<t:= sub_pos.mpr z; let V:= dollar B^n; let F:= payD B (-t); have he:= dollar_op w t ht n; have hv(p:ℝ): payD B p * payD B (-t)=payD B (p-t):= Eq.symm (payD_add B p _); let s:= payD B E; let U':= payD B x
    have hu : ((dollar B)^n*payD B E) = V*F* U' :=by
        rw [mul_assoc V,mul_comm F]; unfold F U'; rw [hv,show x-t=E by unfold t; ring]
    refine ((isBigO_refl V L ).mul p).trans_isLittleO (?_); change ((dollar B)^n*payD B E)=o[L] payD B x; rw [hu]; let H:= IsLittleO.mul_isBigO (isLittleO_const_iff (show (1:ℝ)≠0 from one_ne_zero) |>.mpr he) (isBigO_refl U' L); exact H.congr (fun i=>rfl) (fun i=> (one_mul ( U' i )).symm.symm)
lemma mark_power (w:Rise B L)(p:Consume B L E U)(q: E < n*(-1/2:ℝ)): ∀ d:ℕ, ( (dollar B)^d * U ) =o[L] (( mark B )^n):=by intro d; have he:=payD_pow B (-1/2) n; exact (spendMark w p q d).congr' (.refl ..) (( mark_exp w ).mono fun i hi=> by rw [he,Pi.pow_apply, ← hi,Pi.pow_apply] )
lemma inverseSize (p:payD B (-E) ≤ᶠ[L] U): Consume B L E U⁻¹:=by
     apply IsBigO.of_norm_eventuallyLE; refine p.mono fun i hi=>?_ ; change ‖( U i )⁻¹‖ ≤ _; rw [Real.norm_of_nonneg (inv_nonneg.mpr ((pay_pos ..).le.trans hi)) ]; apply ( ( inv_anti₀ (pay_pos ..) hi ) ).trans_eq; rw [payD_inv,Pi.inv_apply,inv_inv]
lemma berth_pay (p:payD B (-E) ≤ᶠ[L] U): Consume B L (k*E) ( U^k )⁻¹:=by rw [←inv_pow]; exact Consume.power (inverseSize p)
lemma berth_size (p:Consume B L E U): Consume B L (k*E) (U^k):= Consume.power p
lemma extreme (w: Rise B L)(u: Y ≤ᶠ[L] payD B E)(h:∀ᶠ i in L,0 ≤ Y i)(p:0≤β): Consume B L (E*β) (fun i=> Y i^β):=by
    apply Consume.ordered ( h.mono fun i h=>Real.rpow_nonneg h β ); filter_upwards [u,h] with i hi hp; apply ( Real.rpow_le_rpow hp hi p ).trans_eq; rw [payD,← Real.exp_mul, payD]; congr 1; ring
lemma sumPrice (q:J→ι→ℝ)(m:J→ℝ)(S:Finset J)(p:∀ i∈S,Consume B L (m i) (q i)): Consume B L (∑ i∈ S,m i) (∏ i∈ S,q i):=by
    induction S using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.prod_empty]; unfold Consume; rw [payD_zero]
    | @insert i S t ih=> simp only[Finset.sum_insert t,Finset.prod_insert t]; exact Consume.mul (p i (Finset.mem_insert_self ..)) (ih (fun j h=> p j (Finset.mem_insert_of_mem h)))
-- credentials yieldingCheap+ global μ.E offset.Cell pressures.GeometryP.X ℓ charter. All-k purchases from Indie.S.Trail includes gravity costs.
open Stair MergeTrip
local notation "S₀"=> (fun i=> roof R.draws (l i) (c i) (ρ i) (p i))
local notation "Ξ"=>payD B (-E)
structure Angles (e:ℕ)(R:Realm G (e+1) Credit.leanC)(h u:ℕ)(ρ:ι→ℝ)(l b v r c:ι→ℕ)(L:Filter ι)(B:ι→ℝ)(E:ℝ): Prop where
    phase : Consume B L (-E) (( hereD R.draws ρ b )^u)
    horizon : Consume B L (-E) (fun i=> paceT R.draws.S (b i) (v i) ^ h)
    left : Consume B L (-E) (fun i=> R.tempC ( r i ) ( v i ))
    right : Consume B L (-E) (fun i=> R.tempC ( v i ) ( c i ))
variable (f: Rise B L)(H₀:Angles ( G:=G ) e R h u ρ l b v r c L B E)
include H' H₀ f
lemma CheapAngles (u:∃ z>0,payD B (-z) ≤ᶠ[L] hereD R.draws ρ c): ∃ C:ℝ, Cheap Z n L (dollar B) (payD B (-C)) Ξ :=by
   obtain ⟨z,pz,hz⟩:=u; let D:ℕ:= (n+1)*h; let C:ℝ:= E+D*z; refine ⟨C,⟨?_ ,?_, ?_, ?_, ?_⟩⟩
   · have hm : Consume B L (-E) ( ( hereD R.draws ρ c ^ D )⁻¹ * payD B (-C) ) :=by rw [show -E=D*z+-C from by unfold C; ring]; exact Consume.mul ( berth_pay hz ) (isBigO_refl _ L)
     apply Wage.enroll (hm.congr' (?_) (.refl ..)); filter_upwards [H'.frame] with i ⟨_,_,_,hc,_,_,p,_,_⟩; unfold πMark; rw [p,hc]; rfl
   · apply Wage.enroll (H₀.phase.congr' (?_) (.refl ..)); filter_upwards [H'.frame] with i ⟨_,hb,_,_,_,_,p,_,_⟩; unfold πMark; rw [hb,p]; rfl
   · exact Wage.enroll (H₀.horizon.congr' ( H'.frame.mono fun i ⟨_,hb,ht,_,_,_,_,_,_⟩=>by dsimp only; rw [hb,ht] ) (.refl ..))
   · exact Wage.enroll (H₀.left.congr' ( H'.frame.mono fun i ⟨_,_,ht,_,hv,_,_,_,_⟩=>by dsimp only; rw [ht,hv] ) (.refl ..))
   · exact Wage.enroll (H₀.right.congr' ( H'.frame.mono fun i ⟨_,_,ht,h,_,_,_,_,_⟩=>by dsimp only; rw [h,ht] ) (.refl ..))
omit H' H₀ in
lemma peerP_chip {z:ℝ}(w:hereD R.draws ρ c ≤ᶠ[L] payD B (-z)) (h:E≤ z*MS.Tide.mildG) : Wage L (dollar B) Ξ (FVA2.Speed.chip ∘ S₀) := Wage.enroll ( payD_move f (by linarith only [h]:-z * MS.Tide.mildG ≤ - E) ( extreme f w (Eventually.of_forall fun i=>( sizeT_pos _ (p i) _ ).le) MS.Tide.mild_p.le ) )
omit H₀
variable (S₁: Fin (n+1)→ℕ) {D O0:ℕ} (hq:payD B (-β) ≤ᶠ[L] hereD R.draws ρ v)(hw: (∑ i,S₁ i)≤ O0)(v₀: 0<β)
include hq hw v₀
lemma fareCosts : Consume B L (O0*β) (fareU Z S₁):=by
    let Q(i):= ( ( hereD R.draws ρ v )^(S₁ i) )⁻¹; have hx : (∑ i:Fin (n+1),(↑(S₁ i):ℝ)*β)≤ O0*β:=by rw [←Finset.sum_mul]; refine mul_le_mul_of_nonneg_right (?_) v₀.le; exact_mod_cast hw
    refine payD_move f hx ( (sumPrice Q (fun i: Fin (n+1)=> S₁ i*β) _ (?_:∀ i∈ Finset.univ,Consume B L (S₁ i* β) (Q i))).congr' ( ?_ ) (.refl ..) ); · exact fun i _=> berth_pay hq
    filter_upwards [ H'.frame ] with i ⟨_,_,h,_,_,_,w,_,_⟩; unfold fareU billSize markW πMark; rw [Finset.prod_apply]; simp_rw [w,h]; rfl
variable {A' p_ :ℕ}
lemma savings (e1: O0*β+ (-E)< A'*(-1/2:ℝ))(e2:O0*β+(p_+1:ℝ)*(-1/2)<A'*(-1/2)) : (∀ k:ℕ,(fun i=> dollar B i ^ k * (fareU Z S₁ i * Ξ i)) =o[L] ( ( mark B )^ A' )) ∧ ( ∀ k:ℕ,( fun i=> dollar B i^k * (fareU Z S₁ i * (mark B i ^ (p_+1)))) =o[L] ( (mark B)^A' )) :=by
   let U:= fareCosts p Q Z H' f S₁ hq hw v₀; exact ⟨mark_power f (Consume.mul U (isBigO_refl _ L)) e1,mark_power f (Consume.mul U ( Consume.power (n:=p_+1) (penMap f (EventuallyEq.rfl)) )) ( by simpa only [Nat.cast_add,Nat.cast_one] using e2 )⟩ -- Type inference binder
omit H' hq hw v₀ in
lemma O_angle (w:0≤E): Wage L ( dollar B ) 1 (payD B (-E)):= by
    apply Wage.enroll; rw [← payD_zero B]; exact payD_move f (neg_nonpos.mpr w) (isBigO_refl _ L)
end YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
