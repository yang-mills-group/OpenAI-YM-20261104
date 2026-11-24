import YM.FormalBulk08.Spruce.Hush
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I X: Type} {τ:Time X}{f b δ g p k : X→ℝ}
lemma Calm.sum (h:Calm τ δ k b g)(ht:Calm τ δ k f p): Calm τ δ k (fun i=> b i+ f i) (fun i=> g i+p i):= by refine ⟨h.aF.plus ht.aF,h.bF.plus ht.bF,?_⟩; exact (h.diff.plus ht.diff).lower fun i=> le_of_eq (congr_arg _ (by ring))
lemma Calm.growth (h:Calm τ δ k b g)(hp:Pact τ δ f p) : Calm τ δ k (fun i=> f i*b i) (fun i=> p i*g i):= by
    have hv:Faint τ (fun i=>δ i*k i) (fun x=> (f x-p x)*g x):= by
       obtain ⟨C,hC,c,Z⟩:=hp.blur; obtain ⟨A,a,h,U⟩:=h.bF; refine ⟨_, hC.times a,fun x=>mul_nonneg (c x) (h x),fun x=>?_⟩;rw [abs_mul]; refine (mul_le_mul (Z x) (U x) (abs_nonneg _) ((abs_nonneg _).trans (Z x))).trans_eq ?_;ring
    refine ⟨(h.aF.times hp.left).lower (fun i=>le_of_eq (congr_arg abs (mul_comm ..))), (h.bF.times hp.right).lower (fun i=>le_of_eq (congr_arg abs (mul_comm ..))),?_⟩; exact ((h.diff.times hp.left).plus hv).lower fun i=> le_of_eq (congr_arg abs (by ring))
lemma Calm.lapse (h:Calm τ δ k b g)(he:∀ i,k i ≤ p i)(hp:∀ i,0≤δ i): Calm τ δ p b g:= ⟨h.aF.wane he,h.bF.wane he,h.diff.wane fun i=>mul_le_mul_of_nonneg_left (he i) (hp i)⟩
lemma join_faint (u:I→X)(t:Time I)(f z:X→ℝ)(h:Soft t (fun i=> τ.day (u i)))(hp: Faint τ z f): Faint t (fun i=>z (u i)) (fun i=>f (u i)):= by obtain ⟨V,p,H,Q⟩:=hp; exact ⟨_,town_fold h p,fun i=>H _,fun i=>Q _⟩
lemma Calm.lifted (u:I→ X)(t:Time I)(h:Soft t (fun i=>τ.day (u i)))(hp:Calm τ δ k b g): Calm t (fun i=>δ (u i)) (fun i=>k (u i)) (fun i=>b (u i)) (fun i=>g (u i)):= ⟨join_faint u t _ _ h hp.aF,join_faint u t _ _ h hp.bF, join_faint u t _ _ h hp.diff⟩
lemma Calm.quiet (τ:Time X) (δ g : X→ℝ) : Calm τ δ g 0 0 := ⟨faint_zero ..,faint_zero ..,by simp; exact faint_zero ..⟩
lemma calm_sums {f p:I→X→ℝ}(S:Finset I) (h:∀ i∈S, Calm τ δ g (f i) (p i)): Calm τ δ g (fun x=>∑ i∈S,f i x) (fun x=>∑ i∈S,p i x):= by induction S using Finset.induction with
    | empty=>simp only [Finset.sum_empty];exact Calm.quiet ..
    | @insert i S ht ih=>simp_rw [Finset.sum_insert ht];exact (h i (Finset.mem_insert_self ..)).sum (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))

-- prefix clock, base need zero only. no ancestor demands paid beyond window and τ-day
variable {P:Page X}{C:Pin P}
abbrev startP (x:X)(C:Pin P): Deck C:=⟨⟨x,P.ell x,le_rfl⟩,C.land x⟩
def rday (τ:Time X)(C:Pin P): Time (Deck C):= τ.reach fun i=>i.a
def qday (τ:Time X)(C:Pin P): Time (Turn C):= τ.reach fun i=>i.a
abbrev steps (C:Pin P)(i:X):ℕ:= C.N i-P.ell i
lemma raySteps (h: Soft τ (fun i=> sowing (P.mesh i) (P.ell i) (C.N i))): Soft τ (fun i=>(steps C i:ℝ)):= by
    refine (h.times (soft_coin τ (Real.log 2)⁻¹)).below (fun i=>?_); rw [Nat.abs_cast]; apply le_trans _ (le_abs_self _);rw [←div_eq_mul_inv]; apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr; have hh:= sowing_green (P.mesh i) (P.ell i) (steps C i); rwa [show P.ell i+ steps C i=C.N i from (by unfold steps; have:=C.land i;omega)] at hh
lemma tabular (h:Soft τ (fun i=>(sage C).day (startP i C)))(hp:Soft τ (fun i=>sowing (P.mesh i) (P.ell i) (C.N i))) (he:Years P): Soft (rday τ C) (fun i=>(sage C).day i):=by
    obtain ⟨B,b,H⟩:=he.distance
    refine (((soft_coin τ B).times (h.plus hp)).reach (fun i:Deck C=>i.a)).below (fun i=>?_)
    rw [abs_of_nonneg ((sage C).good _)]; apply le_trans (H i.a i.b (P.ell i.a) le_rfl i.zone); refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_right (show sowing (P.mesh i.a) (P.ell i.a) i.b ≤ sowing _ _ (C.N i.a) from ?h) _) b) (le_abs_self _)
    have hh:= sowing_plus (P.mesh i.a) i.cap -- duplicate
    unfold sowing at *; linarith only [hh]
-- abs/faint profile pays with step repeated factor ≤1
lemma tinmoon {k:Deck C→ℝ} {T:Deck C→ℝ}{f:Turn C→ℝ} (hs:∀ i,0≤k i)(ht:∀ x:Turn C,k x.bed ≤ k x.ups)(hp:Faint (qday τ C) (fun i=> k i.ups) f)(hP:Soft τ (fun i=>(steps C i:ℝ)))(hx:∀ x,T (startP x C)=0)(hf:∀ i:Turn C, |T i.ups| ≤ |T i.bed| + |f i|): Faint (rday τ C) k T := by -- h remove
    obtain ⟨V,⟨A,n,ha,H⟩,v,U⟩:=hp; let β (x:X):= A*(τ.day x)^n; have hb x:0≤β x:= mul_nonneg ha (pow_nonneg (τ.good x) _); have hc:Soft τ β:= (soft_coin _ A).times ((soft_day τ).pows n)
    let d (x:Deck C):=x.b-P.ell x.a
    have hh x m (ht:m ≥ P.ell x)(he:m≤ C.N x): let i:Deck C:=⟨⟨x,m,ht⟩,he⟩; |T i| ≤ (d i:ℝ) * β x*k i:= by
       induction ht with
       | refl=> intro i;rw [show T i = 0 from hx x]; rw [abs_zero];exact mul_nonneg (mul_nonneg (by positivity) (hb _)) (hs i)
       | @step j hz' ih=>
          intro i; let u: Turn C:=⟨⟨x,j,hz'⟩,he⟩; have he' := ih (by omega); have hr:d i=d u.bed+1:= Nat.succ_sub hz'
          apply (hf u).trans; rw [hr, Nat.cast_add_one,add_mul, add_mul,one_mul]; refine add_le_add (le_trans he' (mul_le_mul_of_nonneg_left (?H : k u.bed ≤ k i) (mul_nonneg (by positivity) (hb x)))) ((U u).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (H u)) (hs u.ups))); exact ht u
    refine ⟨_,(hP.times hc).reach (fun i:Deck C=>i.a), fun i=>mul_nonneg (by positivity) (hb _), fun i=>?_⟩; refine (hh i.a i.b i.zone i.cap).trans ?_; change (d i:ℝ)*β i.a*k i ≤ _; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?D) (hb i.a)) (hs i); unfold d steps; have := i.cap; omega
lemma coral_clock {k:Deck C→ℝ} {T U:Deck C→ℝ}{V W:Turn C→ℝ}(h:∀ i,0≤k i)(he:∀ x:Turn C,k x.bed≤ k x.ups)(hh:∀ i,0≤δ i)(μ:Turn C→ℝ)(hm:∀ i,|μ i| ≤1)(hp:∀ x,T (startP x C)=0)(hs:∀ x,U (startP x C)=0)
    (hV:∀ i:Turn C,T i.ups= μ i*T i.bed+V i)(hU:∀ i:Turn C,U i.ups= μ i*U i.bed+W i)(hx:Calm (qday τ C) (fun i=>δ i.a) (fun i=> k i.ups) V W)(hP:Soft τ (fun i=>(steps C i:ℝ))): Calm (rday τ C) (fun i=>δ i.a) k T U:= by
    have hK (T:Deck C→ℝ)(f:Turn C→ℝ)(hp:∀ i:Turn C,T i.ups=μ i*T i.bed+ f i)(i:Turn C):|T i.ups|≤|T i.bed|+|f i|:= by rw [hp i];apply (abs_add_le ..).trans; rw [abs_mul]; exact add_le_add_left (mul_le_of_le_one_left (abs_nonneg _) (hm i)) _
    exact ⟨tinmoon h he hx.aF hP hp (hK _ _ hV), tinmoon h he hx.bF hP hs (hK _ _ hU), tinmoon (f:=V-W) (T:=fun i=>T i-U i) (k:=fun i=>δ i.a*k i) (fun i=>mul_nonneg (hh _) (h i)) (fun i=> mul_le_mul_of_nonneg_left (he i) (hh _)) hx.diff hP (fun i=> by rw [hp,hs,sub_self]) (hK (fun i=>T i-U i) _ (fun i=>by rw [hV,hU];simp only [Pi.sub_apply];ring))⟩
end YM.FormalBulk08.Spruce
