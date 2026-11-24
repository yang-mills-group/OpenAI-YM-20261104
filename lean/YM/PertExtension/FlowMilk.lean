import YM.PertExtension.PolyFlow

/-! Paired heat flow tool: changing kernels with negligible errors or only
bounded entries. Covariances need not be nonsingular. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.PertExtension.PolyFlow
open Function Filter Set Finset MvPolynomial Next.Rank Next.Rank.Normal
open scoped Topology Classical BigOperators
variable {ι V :Type*}{l:Filter ι}{f:ι→poly V}{p:poly V}{b:V→ℂ}{q:ι→V→ℂ}{m:ι→ℂ}

lemma empty_close (h:Limit f p l): Close f p 0 l:=⟨h,by simpa only [Pi.zero_apply,zero_smul] using! (Limit.const (p:=(0:poly V)) (l:=l))⟩
lemma rate_as.left_constant {c:ℂ} : rate_as (fun _:ι=>c) c m l := ⟨tendsto_const_nhds,by simpa [sub_self] using! (tendsto_const_nhds (x:=(0:ℂ)))⟩
lemma rate_of_tendsto {c:ℂ}{a:ι→ℂ}:Tendsto a l (𝓝 c) → rate_as a c 0 l:= fun h=>⟨h,by simpa only [Pi.zero_apply,zero_mul] using! (tendsto_const_nhds (x:=(0:ℂ)))⟩

theorem slit_close (h: ∀ i,rate_as (fun k=>q k i) (b i) m l) (r:poly V): Close (fun k=>slit (q k) r) (slit b r) m l:= by
    induction r using MvPolynomial.induction_on with
    | C a=>simp [Close.const]
    | add p q hp hq=> simp_rw [_root_.map_add]; exact hp.add hq
    | mul_X p i hp =>
       simp_rw [mul_comm p _,slit_prod,C_mul'];exact (Close.const (p:=X (σ:=V) (R:=ℂ) i)|>.mul' hp).add ((Close.const (p:=p)).scale (h i))

theorem slit_variable (h: ∀ i,rate_as (fun k=>q k i) (b i) m l)(hp:Close f p m l):Close (fun k=> slit (q k) (f k)) (slit b p) m l:=hp.operator (R:=fun k=>(slit (q k)).toLinearMap) (T:=(slit b).toLinearMap) <| slit_close h

variable {Q : Symmetric V}{K:ι→Symmetric V}
lemma milk_close (h:∀ i j,rate_as (fun k=>(K k).cov i j) (Q.cov i j) m l)(r:poly V) : Close (fun k=>milk (K k) r) (milk Q r) m l:= by
    induction r using MvPolynomial.induction_on with
    | C a=> simp [Close.const]
    | add p q hp hq=> simp_rw [_root_.map_add]; exact hp.add hq
    | mul_X p i hp=> simp_rw [mul_comm p _,feeds];exact (Close.const (p:=X (σ:=V) (R:=ℂ) i)|>.mul' hp).add (slit_variable (h i) hp)
lemma milk_continuity (h:∀ i j,Tendsto (fun k=>(K k).cov i j) l (𝓝 (Q.cov i j)))(hf: Limit f p l): Limit (fun k=>milk (K k) (f k)) (milk Q p) l := hf.operator (R:=fun k=>milk (K k)) (fun r=>(milk_close (fun i j=>rate_of_tendsto (h i j)) r).toLimit)

-- scalar linear read uses finite fence only
lemma Limit.inspect {L:poly V→ₗ[ℂ] ℂ}(h:Limit f p l): Tendsto (fun k=>L (f k)) l (𝓝 (L p)):=by
    obtain ⟨⟨s,hp,hw⟩,he⟩:=h
    have ht := tendsto_finset_sum s (fun i hi=>(he i).smul_const (L (monomial i 1)))
    rw [show L p=∑ i∈s, coeff i p • L (monomial i 1) from ?xe]
    case xe =>
      conv_lhs => rw [terms hp,map_sum]
      simp_rw [map_smul]
    apply ht.congr' (hw.mono fun k hk=>?_) -- orientation
    change (∑ i∈s, coeff i (f k) • L (monomial i 1)) = L (f k)
    conv_rhs => rw [terms hk,map_sum]
    exact Finset.sum_congr rfl fun i _=> (map_smul L _ _).symm
lemma blend_limit (h:∀ i j,Tendsto (fun k=>(K k).cov i j) l (𝓝 (Q.cov i j)))(hf: Limit f p l): Tendsto (fun k=>blend (K k) 0 (f k)) l (𝓝 (blend Q 0 p)) := Limit.inspect (L:=(aeval (0:V→ℂ)).toLinearMap) (milk_continuity h hf)

abbrev Bounded (K:ι→Symmetric V)(l:Filter ι):=∀ x y,∃ c:ℝ,∀ᶠ k in l,‖(K k).cov x y‖≤c
lemma bounded_mean (h:Bounded K l)(r:poly V): ∃ c:ℝ,∀ᶠ k in l,‖blend (K k) 0 r‖≤c:=by
    choose M hM using h
    let v:=r.vars
    let B :ℝ:=1+v.sum fun i=>v.sum fun j=>|M i j|
    have hb:1≤B:=by dsimp [B]; have hz i (hi:i∈v):0≤(v.sum fun j=>|M i j|):=Finset.sum_nonneg fun j _=>abs_nonneg _
                    exact le_add_of_nonneg_right <| Finset.sum_nonneg hz
    have hc i (hi:i∈v) j (hj:j∈v): M i j≤B := (le_abs_self _).trans (by unfold B;refine le_trans ?_ (le_add_of_nonneg_left zero_le_one); exact (Finset.single_le_sum (f:=fun j=>|M i j|) (fun b _=>abs_nonneg _) hj).trans (Finset.single_le_sum (f:=fun i=>∑ j∈v,|M i j|) (by intro;intro;positivity) hi))
    have hh:= (eventually_all_finset v).mpr (fun i _=>(eventually_all_finset v).mpr (fun j _=>hM i j))
    exact ⟨_, hh.mono (fun k hk=> Tapes.bound_v r _ le_rfl hb (m:=0) (fun _ _=>by simpa using! (zero_le_one.trans hb)) fun i hi j hj=>(hk i hi j hj).trans (hc i hi j hj))⟩
lemma blend_fading(h:Bounded K l)(hf:Limit f (0:poly V) l): Tendsto (fun k=>blend (K k) 0 (f k)) l (𝓝 0):=by
    obtain ⟨⟨s,_,hs⟩,hp⟩:=hf
    let S(k):= blend (K k) 0
    let g (i:V→₀ℕ) k:= coeff i (f k)*S k (monomial i 1)
    have he i (hi:i∈s):Tendsto (g i) l (𝓝 0):=by
       obtain ⟨c,hc⟩:=bounded_mean h (monomial i 1)
       simp_rw [coeff_zero] at hp
       have ht:= (hp i).norm.mul_const c
       rw [norm_zero,zero_mul] at ht
       refine squeeze_zero_norm' (hc.mono fun k hk=> ?_) ht
       exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
    have ht:Tendsto (fun k=>∑ i∈s,g i k) l (𝓝 0):=by simpa only [Finset.sum_apply,Finset.sum_const_zero] using! tendsto_finset_sum s he
    exact ht.congr' (hs.mono fun k hk=>by
        change (∑ i∈s, g i k)=S k (f k)
        conv_rhs => rw [terms hk,map_sum]
        simp_rw [map_smul,smul_eq_mul]
        rfl)
end YM.PertExtension.PolyFlow
