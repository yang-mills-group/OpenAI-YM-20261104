import YM.RG05Readout.Harvest.Tissue
/-!
# Powered real readout on supported WM profiles

Output restores field costs and Gate.Summation on all roots.From TRUE
 F product + counter term through u with Φ. `Threshold` Z*b parity.
 Does not assert any future estimate in prices on perturbative kernels.
 Cost useful in detection. Presence on any accepted layout, text above.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k ℓ t:ℕ}{e Q z x R a η:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "F₁"=> Site (C.side (n+1) p)
local notation "Y!"=> C.side (n+1) p
variable {D:Address.Rail C}{V I:Type}[DecidableEq V][Fintype V] {P: Address.Sight C d p} (S: Address.Emblems C d) (hm: n+1 < m)(hv:b ≤ n)(hN:m ≤ N)(ht:j ≤ b)
local notation "h₁"=>hm.le.trans hN
local notation "h₂"=> n.le_succ.trans hm.le
local notation "h₃"=> hv.trans n.le_succ
local notation "k!"=> (ht.trans (hv.trans n.le_succ)).trans (hm.le.trans hN)
local notation "Ω"=> Grip C p N n m b d j hm hv hN ht S
local notation "T₁"=> GridApprox.tilesAt C.S p k!
variable (s:V→ℕ) (x:(i:V)→Palette C (s i)) (U:(i:V)→ Emblems C (s i))
local notation "c!"=> n+1
local notation "f₁"=> fun i:V=>Many.point (U i) (x i) m N
variable (F : Wave V) (g :Body) (r:ℝ)
local notation "X"=> constellation (C:=C) s f₁ r F h₁ m
variable (hz:r*R+ 2*C.S.a (n+1)< C.S.radius p)(htP:z+r*R< C.S.radius p)
    (hξ:∀ x∈ tsupport F.val,∀ i:V,‖x i‖≤ R)(hr:0<r)
local notation "uπ"=> Λ h₃ p
local notation "φ"=> physicalEra r F g C m p N s f₁
noncomputable def rebases (C:Family G)(n m d:ℕ) :ℝ:= (C.S.a (n+1)/C.S.a m)^d
noncomputable def reimburses (C:Family G)(n b d:ℕ):ℝ:= ((C.S.a b)^4)*((C.S.a (n+1))/C.S.a b)^d
local notation "μ"=> (↑(reimburses C n b d):ℂ)
local notation "a!"=> rebases C n m d
local notation "v!"=> (↑(rebases C n m d):ℂ)
local notation "Q₁"=> fun x=> fieldC C m N p d (Many.point S x m N) g
variable (M:Palette C d)(F':Bin G (C.side N p))
variable (hg:∀ x∈tsupport g.val,‖x‖≤ z)(hH:z+C.S.a b≤ C.S.a j/4)(hψ:z+C.S.a b*3< C.S.radius p)
-- price normalization compensated for output weight
lemma ratio_back : μ * ratioX (uπ) d=(A c!:ℂ)^4:=by
     unfold reimburses ratioX; push_cast; let v:ℝ:= (uπ).count.val; let V:ℂ:= (v:ℝ); have hp:v ≠0:=by unfold v; exact_mod_cast (uπ).count.property.ne'
     have hV:Complex.ofReal v ≠0:=Complex.ofReal_ne_zero.mpr hp; have hi: (C.S.a (n+1):ℂ) ≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'; have he:(A b:ℂ)=(A c!:ℂ)*(v:ℂ):=by exact_mod_cast (C.S.embeds_scale _).symm
     change _*(V^d/V^4)=_; rw [he]; unfold V; field_simp; rw [← mul_pow,div_mul_cancel₀ _ hV,one_pow]
-- scalar command for comparing n+1.Pieces. Pull derivative powers remain d
include hN
lemma chartC (i:ℕ)(M:Palette C d): fieldC C i N p d (Many.point S M m N) g=fieldC C m N p d (Many.point S (((A i:ℂ)/(A m:ℂ))^d •M) m N) g:=by
     simp only [weave_fine hN,map_smul]; rw [field_translate]; let X':= (finer S hN M); unfold fieldC; rw [smul_smul]; apply congr_arg (· • _); unfold Pulse.gate; have he:(A m:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'; simp_rw [div_pow]; field_simp
lemma chart_issue : Q₁ (v! • M)= fieldC C c! N p d (Many.point S M m N) g:=by push_cast [rebases]; exact (chartC S hN g _ M).symm
-- unscaled→on physical moments.Signs and measure includes capture/counter.K
section consumers
include hψ hg htP hr hz hξ
variable {M} {Rg:ℝ}
set_option maxHeartbeats 700000 in
lemma what_cut (hp:Ω (X) M Q e Rg):
     let Z:= chip C p N n m d h₁ S X M
     φ-Q₁ (v! • M)= μ • gathered C (n+1) N p d h₁ Z b g:=by
   intro Z; let v := Many.point S M m N; let W:= crops C N p N d le_rfl (precinct C p N d v) (n+1) h₁; let Y₀ i:= restricted C c! p i g
   have hR:z+A c!*3<C.S.radius p:=by have h:= C.S.strictAnti.antitone h₃; linarith only [h,hψ]
   rw [mass h₁ Z hp.silent' g hg h₃ hψ]; rw [Finset.smul_sum]
   rw [chart_issue S hN g M]
   rw [← return_weight (d:=d) v (le_refl (n+1)) g h₁ hg hR] -- expand chart_counter equals gather at same.P
   rw [show gathered C c! N p d h₁ W c! g= ∑ y:F₁, stepUp t! ((Λ h₁ p).embed y) (W (Y₀ y)) from (Finset.sum_congr rfl (fun i _=> by unfold uniform;rw [dif_pos le_rfl,crops_head]))]
   rw [registry s f₁ r F h₁ hr hξ hz htP g (by linarith only [hR,C.S.a_pos (n+1)]) (fun x hx=> hg _ (subset_closure hx)),Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [smul_smul,ratio_back hv]; let a:= (Λ h₁ p).embed i; let g':= Y₀ i; rw [show stepUp t! a (Z g')=stepUp t! a (X g')- stepUp t! a (W g') from rot_sub ..]; rw [smul_sub] -- order?
include h hH
lemma render (he:0≤e)(hp:Ω X M Q e Rg)(hT:Tall (E:=E4) g (d+2) 1 1):
     let T:=T₁; let U:= φ-Q₁ (v! • M)
     Interior (T.chamber 0) U ∧ T.rootTest (C.beta N p) U≤ reimburses C n b d*((A j/A b)^4)*e:=by
   intro T O; let Z:=chip C p N n m d h₁ S X M; have hzX:=valueSum (p:=p) ht h₁ Z hp.silent' g hg hH h₃ h he (fun i hi=>hp.presence i ((Finset.mem_filter.mp hi).2) (restricted C b p i g) (fun j' hj y _=> by
       unfold restricted; rw [Native.pulled,norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _)]; apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (C.S.a_pos _).le (by have h₀:= C.S.strictAnti.antitone (Nat.zero_le b); simpa only [Schedule.a_zero] using h₀))).trans; exact (hT j' hj (C.S.place i+ (C.S.a b) • y)).trans_eq (by simp)))
   unfold O; rw [what_cut S hm hv hN ht s x U F g r hz htP hξ hr hg hψ hp,Next.Extract.root_smul]; exact ⟨hzX.1.scale _, (mul_le_mul_of_nonneg_left hzX.2 (norm_nonneg _)).trans_eq (by
         have ht:0<reimburses C n b d:=by unfold reimburses; have hx:= C.S.a_pos (n+1); have h:= C.S.a_pos b; positivity
         simp [Real.norm_of_nonneg ht.le,mul_assoc])⟩ -- arguments
end consumers
end YM.RG05Readout.Harvest
