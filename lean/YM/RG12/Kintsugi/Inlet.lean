import YM.RG12.Kintsugi.Barge
import YM.Extra.WILSON_STARTUP.Fast
import YM.RG12.Common.Capture
/-! # Sharp Inlet on Ward protected fields, d=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Set Function MeasureTheory Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank Next.Rank.Perch
open Next.Rank.Atlas Next.Rank.East MergeProof MergeProof.East Source UVNext.FreeStress
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff)
variable (hS:Ranked P) (T:MaxwellData C)
local notation "χ"=>C.path.levels.clock.hatBeta

def Worthy {d:ℕ}(x:S.Field d)(p k:ℕ):Prop:=∃ v:C.label d,S.project d (M d k v)=x ∧ mass C d v ≤ χ k^p
include h hS
lemma good_in (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) (hG:G.Simple) (i j:Axis):
   let x:=reCenter S U.sector.energy i j
   ∀ᶠ k in atTop,lit k → Worthy M x 9 k:= by
   intro x
   by_contra! heq
   obtain ⟨T,hK,hT⟩:= oracle (C:=C) hG
   have hB:∃ᶠ k in atTop, ¬ Worthy M x 9 k ∧ lit k:=heq.mono fun _ h=> ⟨h.2,h.1⟩
   obtain ⟨g,Z,hg,hA,X,hX⟩:= rooted U M P h hS T H he hf hG _ hB
   obtain ⟨R,hR⟩:=lines T.hT _ T.lit.edges T.lit.hers
   obtain ⟨K,He,Ha,Hs,Hk⟩:= zooms U M P T (fun i=>(hA i).2.2) hX R hR
   obtain ⟨w,hw⟩:= persistent U T K hT Ha Hs
   have hP:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hw i) j
   let x₀:=(((T.T.κ)⁻¹ • T.T.J): (Bel C.book).Stress) i j
   change Tendsto (fun l=> (K.U (w l) 4).symm ((K.r (w l))^4 • x)) atTop (𝓝 x₀) at hP
   let l:= ‖x₀‖+1
   obtain ⟨t,ht,hz⟩:= price_nearby (S:=S) hG U M T R
   obtain ⟨k,h4,h₁,hq,hN,hL,hV,hD⟩:= (eventually_all_hot (b:=fun t => ‖(K.U t 4).symm ((K.r t)^4 • x)‖≤l) (w:=w) (g:=g) («χ»:=χ) hg (hat_grows (C:=C) hG) (Hk 3) (Hk 4) (Hs.units 3) (hP.norm.eventually (ge_mem_nhds (show ‖x₀‖<l by dsimp [l];linarith))) (C.ref 4) (t*l)).exists
   have hB:=hA (w k)
   obtain ⟨v,hv,hv'⟩:=hz _ _ _ _ hB.2.2 h4 (K.U (w k) 3) h₁ hV (K.U (w k) 4) hq (he.unit 4 (g (w k)) hD)
      x
   specialize hX (w k)
   change mass C 4 v ≤ t*(χ (g (w k)))^8 * ‖(K.U (w k) 4).symm (Next.Rank.Station.gap _ _ _^4 • x)‖ at hv'
   rw [← hX,← He] at hv'
   let β:= χ (g (w k))
   apply hB.1; refine ⟨v,hv,hv'.trans ?_⟩
   change t*β^8*_ ≤ β^9
   have hP: 0≤β^8:=by positivity
   rw [pow_succ]
   exact (mul_le_mul_of_nonneg_left hN (mul_nonneg ht.le hP)).trans ((le_of_eq (show t*β^8*l=β^8*(t*l) by ring)).trans (mul_le_mul_of_nonneg_left hL hP))
where eventually_all_hot {w: Extraction.Sequence}{g:ℕ→ℕ}{«χ»:ℕ→ℝ} {p q y b : ℕ → Prop}
    (h₁:Tendsto g atTop atTop)(h₂:Tendsto «χ» atTop atTop)(h₃:∀ᶠ k in atTop,p k)(h₄:∀ᶠ k in atTop,q k)(hU:∀ᶠ k in atTop,y k)(hN:∀ᶠ k in atTop,b (w k))(c:ℕ)(t:ℝ) :
   ∀ᶠ k in atTop,4≤w k ∧ p (w k) ∧ q (w k) ∧ b (w k) ∧ t ≤ «χ» (g (w k)) ∧ y (w k) ∧ c ≤ g (w k) :=
    (w.cofinal.eventually_ge_atTop _).and ((w.cofinal.eventually h₃).and ((w.cofinal.eventually h₄).and (hN.and (((h₂.comp (h₁.comp w.cofinal)).eventually_ge_atTop _).and ((w.cofinal.eventually hU).and ((h₁.comp w.cofinal).eventually_ge_atTop _))))))
end YM.RG12.Kintsugi
namespace YM.RG12.Kintsugi
open Filter Set Function MeasureTheory Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank Next.Rank.Perch
open Next.Rank.Atlas Next.Rank.East MergeProof MergeProof.East Source UVNext.FreeStress Commission
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff) (hS:Ranked P)
local notation "χ"=>C.path.levels.clock.hatBeta
include h
lemma the_price_in {d p:ℕ}(H:Observing C U.room.cutoff ϕ M)(hG:G.Simple)(x:S.Field d)(hX:∀ᶠ k in atTop,lit k → Worthy M x p k):∀ᶠ k in atTop,Worthy M x (p+1) k:=by
   filter_upwards [h.covered.1.eventually hX,h.covered.2.2 d,h.scope,h.covered.1.eventually_ge_atTop (C.ref d)] with k he hv hk hp
   let i:=P.rate k
   obtain ⟨v,hv1,hv2⟩:=he hk
   let r:=C.S.a i / C.S.a k
   obtain ⟨A,hA⟩:= passage U.room.cutoff H hp hv.1
   obtain ⟨w,rfl⟩:= hA.inv.2 v
   have hr:0 < r:=div_pos (C.S.a_pos _) (C.S.a_pos _)
   have hR: r ≤ χ k:= hv.2.1
   have hY : 1 ≤ χ k:= (C.path.levels.fits.delayed k).le
   refine ⟨(↑(r⁻¹^d):ℂ) • w,?_,?_⟩
   · rw [map_smul,map_smul, ← hv1]
     have hc := hA.pulls w
     have hc' : (M d (P.rate k)) (A w) = ((↑(r⁻¹^d):ℂ)) • M d k w := by
        have h₀(x): ((C.S.a x:ℝ):ℂ)≠0:=by exact_mod_cast (C.S.a_pos x).ne'
        rw [← inv_smul_smul₀ (pow_ne_zero d (h₀ i)) ((M d i) _),hc,smul_smul]
        congr 1; unfold r; push_cast; field_simp; rw [div_pow]
     rw [hc',map_smul]
   rw [supplies_mass,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hr).le _)]
   refine (mul_le_mul_of_nonneg_left (hA.lower w) (pow_nonneg (inv_pos.mpr hr).le _)).trans ?_
   rw [inv_pow,← mul_assoc,show (r^d)⁻¹ * (C.S.a (P.rate k)/C.S.a k)^(d+1)=r from by rw [← show r=C.S.a (P.rate k)/C.S.a k from rfl,pow_succ,inv_mul_cancel_left₀ (pow_ne_zero _ hr.ne')],pow_succ]
   rw [mul_comm r]; exact mul_le_mul (hv2.trans (pow_le_pow_left₀ (hratio _ _) (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos hG).le hv.1) _)) hR hr.le (pow_nonneg (zero_le_one.trans hY) _)
where hratio (C:Family G)(j:ℕ) : 0 ≤ C.path.levels.clock.hatBeta j:=zero_le_one.trans (C.path.levels.fits.delayed _).le

include hS
lemma cent_in (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) (hG:G.Simple) (i j:Axis):
   ∀ᶠ k in atTop,Worthy M (reCenter S U.sector.energy i j) 10 k:=the_price_in U M P h he hG _ (good_in U M P h hS H he hf hG i j)
lemma stress_in (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) (hG:G.Simple) (i j:Axis):
    ∀ᶠ k in atTop,Worthy M (U.sector.energy i j) 11 k:=by
   let x:=U.sector.energy i j; let z:=expectation S 4 x
   filter_upwards [cent_in U M P h hS H he hf hG i j,eventually_ge_atTop (C.ref 4),(hat_grows (C:=C) hG).eventually_ge_atTop (1+‖z‖)] with k hk hv ht
   let u:=unitVec (C.labels.level 4) C.path k; let t:= χ k
   obtain ⟨v,hv,hc⟩:=hk -- shadow hv
   change S.project _ _ = centering S 4 x at hv
   refine ⟨v+z • u,?_,?_⟩
   · rw [map_add,map_add,hv,map_smul,he.unit _ _ (by assumption),map_smul,value_center]; change _ - (z • S.unit 4)+(z • S.unit 4) = _; rw [sub_add_cancel]
   have hl: C.S.a k ≤ 1:= ((C.S.strictAnti.antitone (Nat.zero_le k)).trans_eq C.S.a_zero)
   apply le_trans (b:=t^10 + ‖z‖) ((solid_mass ..).trans (add_le_add hc ?_))
   · have he:1 ≤ t:=le_trans (by linarith [norm_nonneg z]) ht
     rw [show (χ k)^11=t^10*t by unfold t;rw [← pow_succ]]
     nlinarith only [show 1+‖z‖ ≤ t from ht,show 1 ≤ t^10 from one_le_pow₀ he,norm_nonneg z]
   rw [mass_unit]; exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (C.S.a_pos _).le hl)
end YM.RG12.Kintsugi
