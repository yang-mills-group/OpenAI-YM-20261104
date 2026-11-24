import YM.UVExt.CoinGrowth

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Precision RG Lattice Wilson Matrix Laurent Tree Exterior Bid Tensor Set Function Next.Free
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {N:Supply.Rolls s} {Q : PostCost N} {H : ChartRatio G} (K : Kin M H)
    (h : Discipline P A M) (hk : K.Planned Q) (u : ℕ→ℕ) (hu : Tendsto u atTop atTop) (v : ℕ→ℕ) (hv : Tendsto v atTop atTop)
    {U V : ℕ→Shadow G} (hU : ∀ m, woodPassing K u m U) (hV : ∀ m,woodPassing K v m V)
    {X : (i:ℕ)→Transfers A i} (hX : Follows A u M X)

variable {x y : ℕ→ℝ}
def expFee (n : Side) (γ : ℝ) := Real.exp (-γ*n.val)
lemma expfee_tendsto (N : ℕ→Side) (hN : Tendsto (fun i:ℕ=>(N i).val) atTop atTop) (c : ℝ) (h : 0<c) (j : ℕ): Tendsto (fun k=> ((N k).val:ℝ)^j*expFee (N k) c) atTop (𝓝 0) := by
    have ht:=((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s:=(j:ℝ)) c h).comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hN)); unfold expFee; exact ht.congr fun b=> by dsimp only [Function.comp_apply]; rw [Real.rpow_natCast]
lemma weight_limit (N : ℕ→Side) (h : Tendsto (fun i:ℕ=>(N i).val) atTop atTop) (d c D K Q : ℝ) (hc : 0<c) (hd : 0<d)
    (hm : ∀ i:ℕ, 4≤(N i).val → d*((N i).val:ℝ)^2*|K| ≤ D*(N i).val + Q * ((N i).val:ℝ)^4*expFee (N i) c) : K=0 := by
   have ht : Tendsto (fun i=> (D/d)* ((N i).val:ℝ)⁻¹ + Q/d*((N i).val:ℝ)^2*expFee (N i) c) atTop (𝓝 0) := by
       simpa only [add_zero,mul_zero,mul_assoc,Nat.cast_ofNat,Function.comp_apply] using ((tendsto_const_nhds (x:=D/d)).mul ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp h)) |>.add ((expfee_tendsto _ h c hc 2).const_mul (Q/d))) -- tendsto_inv signature
   apply abs_eq_zero.mp ((abs_nonneg K).antisymm' ?_); apply ge_of_tendsto ht
   apply (h.eventually (eventually_ge_atTop (4:ℕ))).mono fun i hi=> ?_
   try dsimp only []
   let n := ((N i).val:ℝ); have npos : 0 < n := by unfold n; exact_mod_cast (N i).property
   have hA := ((le_div_iff₀' (a:=|K|) (mul_pos hd (pow_pos npos 2))).mpr (hm i hi))
   change |K| ≤ _; refine hA.trans_eq ?_; unfold n at *; field_simp [npos.ne',hd.ne']

include h hk K hU hV hX hu
lemma ruby_equal (m p) (x y : ℝ) (w : Dir G (A.S.side m p)) (hv : Tendsto v atTop atTop) (hx : confluent K u v 2 p) :
      ruby K hU hV x y m p w=(x-y) * Tensor.diagonal ((hU m).economicTensor (A.S.side m p) 2) w := by
      obtain ⟨t,ht,hℓ⟩:= h.figure
      obtain ⟨ℓ,h'⟩ := hℓ m
      have hq := KinHarbor K h hk _ u hu ht h'; have hp := KinHarbor K h hk _ v hv ht h'
      let n:=A.S.side m p
      have hE := center_equal (m:=m) hq (hU m) p; have hE' := center_equal hp (hV m) p
      obtain ⟨z,hz,hz'⟩ := hx m 2 le_rfl
      have he : ((hU m).planeTensor n 2) = ((hV m).planeTensor n 2) := (show ((hU m).planeTensor n 2)=z from tendsto_nhds_unique ((hU m).mainLimit n 2).1 hz).trans (tendsto_nhds_unique hz' ((hV m).mainLimit ..).1)
      unfold ruby; simp_rw [hE,hE']; rw [he]; ring

include hv
variable (hp : ∀ i,Tendsto (fun j=>K.alpha (u j) i) atTop (𝓝 (x i))) (hp' : ∀ i,Tendsto (fun j=>K.alpha (v j) i) atTop (𝓝 (y i))) (hN : LocalRatio H)
    (hh : ∀ d,confluent K u v 4 d)
include hp hp' hN hh
set_option maxHeartbeats 200000 in
lemma alpha_pair (hG : Nonempty G.ColorIndex) (m : ℕ) : x m=y m := by
    obtain ⟨c⟩ := hG
    let a : G.Color := EuclideanSpace.basisFun G.ColorIndex ℝ c
    have ha : ‖a‖=1 := OrthonormalBasis.norm_eq_one .. -- edit
    let n p := A.S.side m p; let α p : ℝ := (n p).val; let t := x m-y m; let d := (jclip A m).direct; have hd : 0<d := (jclip A m).quadratic_pos
    let Δ (p) := loopDrift K (m:=m) (p:=p) hU hV; let Δ' p:=loopDrift K (m:=m+1) (p:=p) hU hV ∘ mapBind A M X m p
    let γ := Q.c (A.clock.J (m+1)); let C := 16*Q.Γ (A.clock.J (m+1))* A.clock.loopCap (m+1); let D := postal A P m
    have hm (p) (hs : 4≤(n p).val) : d*((n p).val:ℝ)^2*|x m-y m| ≤ postal A P m * (n p).val + C* ((n p).val:ℝ)^4 * expFee (n p) γ := by
       obtain ⟨l,ht,hℓ⟩:= h.figure; obtain ⟨ℓ,h'⟩ := hℓ m
       have hQ := tone_lower_fixed (KinHarbor K h hk _ u hu ht h') (hU m) ha p hs
       let o (z : ℂ) := melody a (n p) z
       let B w := Tensor.diagonal ((hU m).economicTensor (A.S.side m p) 2) w
       let rub := ruby K hU hV (x m) (y m) m p; let s := dust (A:=A) Q m p
       have hx (z : ℂ) (hz : ‖z‖≤1) : |rub (o z) + Δ p (o z) - Δ' p (o z)| ≤ 8*s := by
           let t := broadcast 1 a z; let w : TypeFace 1→G.ColorIndex→ℂ := fun _ _=>0
           have hv0 := drift_eq K h hk u hu v hv hU hV hX hp hp' hN hh m p (step 0) 0 t w (tone_price a _ ha hz) (fun _ _=>by simp [w])
           have hrew : wave (G:=G) (c:=n p) (step 0) t + wave 0 w = o z := by rw [show wave (step 0) t=o z from (melody_is ..).symm]; exact (congr_arg (o z + ·) (funext fun x=>by unfold Precision.wave; unfold w; simp; rfl)).trans (add_zero _)
           change |rub (o z)+Δ p _-Δ' p _| ≤ _
           change |rub (_ : Dir G (n p)) + Δ p (_ : Dir G (n p)) - Δ' p (_ : Dir G (n p))| ≤ _ at hv0
           convert hv0 using 1 <;> (rw [hrew])
       have heq (z : ℂ) : rub (o z)= t* B (o z) := ruby_equal K h hk u hu v hU hV hX m p _ _ _ hv (fun i=> ((hh p i).mono (by omega))) -- wrong argument order inspect
       have ht z hz := stripe_fee K h u hu v hU hV hX m p _ _ z a ha hz hs (hx z hz)
       have hpos : 0≤ B (o 1) + B (o (Complex.I)) := (mul_nonneg hd.le (sq_nonneg _)).trans hQ
       change d*α p^2*|t| ≤ _
       change d*α p^2 ≤ B (o 1)+B (o (Complex.I)) at hQ
       have hN : (Fintype.card (Site (n p)):ℝ)=((n p).val:ℝ)^4 := by rw [site_card,Nat.cast_pow]
       calc
         _ ≤ |t*(B (o 1)+B (o Complex.I))| := by rw [abs_mul t,abs_of_nonneg hpos,mul_comm]; exact mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
         _ ≤ |rub (o 1)|+|rub (o Complex.I)| := (by rw [mul_add t, ← heq 1, ←heq .I]; apply abs_add_le)
         _ ≤ 2*(postal A P m/2 * α p + 8*s) := (add_le_add (ht 1 (by norm_num)) (ht .I (by simp))).trans_eq (by ring)
         _ = _ := by unfold s C γ dust tolerance expFee; rw [hN]; unfold α; ring
    apply sub_eq_zero.mp <| weight_limit (n ·) ?_ d γ (postal A P m) (x m-y m) C (Q.posC _) hd hm -- binder N
    exact tendsto_atTop_mono (f:=fun p=>(A.S.period p).val) (fun i=> Nat.le_mul_of_pos_right _ (A.S.denominator m).property) A.S.period_strict.tendsto_atTop

end YM.UVExt.Paths
