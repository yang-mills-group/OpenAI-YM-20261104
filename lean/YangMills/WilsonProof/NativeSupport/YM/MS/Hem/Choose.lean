import YM.MS.Hem.Choose
import YM.MS.Hem.Muses
/-!
# Γ algorithm for η−dimε. Exact for Laurent coefficients; pole iff resonance.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W S: Mob G} {x:ℂ} {b:Bool} {r k:ℤ}
-- bulk $h=4$, mark h, including antifield weight

@[simp] lemma vampV (z:ℂ)(n:ℕ): vamp z n 0= -(n:ℂ):= by simp [vamp,toll]
@[simp] lemma vamp0 (n ℓ:ℕ): vamp 0 n ℓ= -(n:ℂ):= by simp [vamp,toll]
lemma vampF (n ℓ:ℕ)(d:Set ℂ): Forest d fun i=>vamp i n ℓ := by intro z hz; unfold vamp toll; fun_prop
lemma vamp_fit (n ℓ:ℕ): ∃ R:ℝ,0<R∧∀ i∈disc R, (1/2:ℝ) ≤ (vamp i n ℓ).re+(n+1:ℕ):= by
    let f (p:ℂ):ℝ:=(vamp p n ℓ).re+(↑(n+1):ℝ); have ht : Continuous f:= by unfold f vamp toll; fun_prop
    obtain he : {i:ℂ|1/2<f i}∈𝓝 0:= ht.continuousAt.tendsto (lt_mem_nhds (show 1/2<f 0 by unfold f; simp; norm_num)); obtain ⟨R,hr,hp⟩:= Metric.mem_nhds_iff.mp he; exact ⟨R,hr,fun i hi=> le_of_lt (hp hi)⟩
lemma vamp_up (n ℓ:ℕ): ∀ᶠ i in dotty,0<(vamp i n ℓ).re+(n+1:ℕ):= by obtain ⟨R,hr,hp⟩:= vamp_fit n ℓ; exact ((show ∀ᶠ i in dotty,i∈disc R from dotty_bill hr).mono fun p h=> lt_of_lt_of_le (by norm_num: 0 < (1/2:ℝ)) (hp _ h))
lemma Vamp_m {j n:ℕ}(h:j≠n)(ℓ:ℕ): ∃ R:ℝ,0<R∧∀ i∈disc R,vamp i n ℓ+j≠0:= by
   let V(p:ℂ):=vamp p n ℓ+j; have hx:Continuous V:= (by unfold V vamp toll; fun_prop); have hV: V 0≠0:= by simp [V,neg_add_eq_zero,Ne.symm h]
   obtain ⟨R,hr,hp⟩:= Metric.mem_nhds_iff.mp (hx.continuousAt.eventually_ne hV); exact ⟨R,hr,fun i hi=>hp hi ⟩
lemma Vamp_high {n ℓ:ℕ}(hv:0<ℓ)(x:ℂ)(hx:x≠0): vamp x n ℓ+n = (-2*ℓ) * x ∧ vamp x n ℓ+n ≠ 0:= by
    let V:= ℓ; have he : vamp x n ℓ+n=(-2*ℓ)*x:= by unfold vamp toll; ring
    rw [he]; simp [hx,hv.ne']
lemma vamp_room (h:ℕ)(ℓ:ℕ)(ht:0<ℓ): ∀ᶠ i in dotty, ∀ n<h+1, vamp i h ℓ+n≠0:= by
    have he (n:ℕ): ∀ᶠ i in dotty,vamp i h ℓ+n≠0:= by
       by_cases hr:n=h; · subst n; exact dotty_non.mono fun t ht'=> (Vamp_high ht t ht').2
       obtain ⟨R,hu,hV⟩:= Vamp_m hr ℓ; exact (show ∀ᶠ x in dotty,x∈disc R from dotty_bill hu).mono fun i hi=> hV i hi
    simpa only [Finset.mem_range] using (eventually_all_finset (Finset.range (h+1))).mpr (fun i (_:i∈Finset.range (h+1))=> he i)

variable {f:ℂ→Mob G}{n j ℓ:ℕ}
lemma ferry (h:mer f)(j:ℕ): mer (fun i=> Tad (f i) j):= by
   obtain ⟨m,H,g,T,hT,h',Hq,rfl⟩:=h; have hm:=tad_hol g h' j; refine ⟨ m,_,Lift.congr (Lift.trim hm hT) ?_⟩; filter_upwards [Hq] with t ht; rw [ht]; exact t_pose _ _
lemma Cycl {u:ℂ→Mob G}(hp:mer u)(ht:0<ℓ) : mer (fun z=> (vamp z n ℓ+j)⁻¹ • u z):= by
   by_cases he:j=n; · subst j; obtain ⟨v,hv⟩:=hp; refine ⟨v+1,?_⟩; unfold altitude; rw [PayRight]; refine Live.congr ( Live.static hv ((-2*(ℓ:ℂ))⁻¹)) ?_; filter_upwards [dotty_non] with z hz; simp only [paid, pow_one,(Vamp_high (n:=n) ht z hz).1]; rw [mul_inv_rev _ z]; change (-2*(ℓ:ℂ))⁻¹ • (z^v) • u z=z • z^v • (z⁻¹ * (-2*(ℓ:ℂ))⁻¹) • u z; rw [mul_smul, smul_comm z, smul_inv_smul₀ hz, smul_comm _ (z^v)] -- parse
   obtain ⟨R,hr,hc⟩:= Vamp_m he ℓ; exact hp.high (x:=fun z=>(vamp z n ℓ+j)⁻¹) (fun i hi=> (( vampF n ℓ _ i hi).add_const (j:ℂ)).inv (hc i hi)) hr -- differentiableAt-add named

def cPos (n:ℕ) (x:ℂ)(F:Mob G): Mob G:= ∑ i∈Finset.range n,(x+i)⁻¹ • Tad F i -- j redundant remove
lemma added_p (hp:mer f)(n m:ℕ)(he:0<ℓ): mer (fun i=> cPos n (vamp i m ℓ) (f i)):= by
    induction n with
    | zero=> unfold cPos; simp only [Finset.range_zero,Finset.sum_empty]; exact mer.zero
    | succ n ih=>
       unfold cPos; simp_rw [Finset.sum_range_succ]; exact mer.add ih (Cycl (ferry hp n) he)
def Bless (n ℓ:ℕ)(i:ℂ)(F:Mob G): Mob G:= progress (n+1) (vamp i n ℓ) F + if ℓ=0 then 0 else cPos (n+1) (vamp i n ℓ) F
lemma blessed (n ℓ:ℕ)(hp:mer f): mer (fun i=> Bless n ℓ i (f i)):= by
   obtain ⟨R,hr,hV⟩:= vamp_fit n ℓ; have hm:= prog_mer (f:=f) hp hV (by norm_num :0<(1/2:ℝ)) (vampF n ℓ _) hr; by_cases h:ℓ=0; · simpa only [Bless,h,if_true,add_zero, vampV] using hm -- simp h not both sides?
   unfold Bless; simp only [if_neg h]; exact mer.add hm (added_p hp _ n (Nat.pos_of_ne_zero h))
end YM.MS.Hem.Mell
