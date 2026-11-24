import YM.LocalTaylorR2.Reel.Stamp
import YM.LocalTaylorR2.Reel.Pend
/-! # Actual E feedthrough. All degrees polynomial in that remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle

lemma sprout_along (x t: Scroll G f)(a:ℝ)(i:LogIndex c f): sprout H (x + a • t) i=sprout H x i + a • (sprout H (x+t) i - sprout H x i):= by
  by_cases h: ∃ j:ℕ, i= .inl (.inl j)
  · obtain ⟨i,rfl⟩:=h; funext F X w; let Y:=X.input (Vine.worldZ X R.beta w); let C:= (X.enforce (2*o.a) (Vine.worldZ X R.beta w) (X.plaza (space T 0 X.B R (.inl i))))
    let u (g:Config G f→ℝ):= -(masked R.p.threshold (R.activities.reg i).support g Y) * C
    change u ((x+a • t) i)=u (x i)+ a*(u ((x+t) i)-u (x i)); unfold u; by_cases he:Healthy R.p.threshold (R.activities.reg i).support Y <;> simp [he]; ring
  push Not at h; have he (j:ℕ):Opacity.key S j≠ identityLog (S:=S) i:= fun hx=> h j (scenic_inj hx.symm)
  rw [alone H (x+a • t) x i he,alone H (x+t) x i he, sub_self,smul_zero,add_zero]

variable {Iota: Type*}
lemma sprout_filled {U : Support c} (w:Iota→ℝ)(p p':Iota)(hp:w p=0)(hv:w p'=1)
   (y t:Reel.Scroll G f)(Q':∀ i:Iota,Cash W s μ L Q o C T (bend R (y + w i • t)))
   (i:LogIndex c f)(hU:H.supportP (identityLog i)⊆ U): Filled (Pop H U) 1 w (fun j:Iota=> sprout H (y + w j • t) i):= by
   let A:=Pop H U; have h (u:Reel.Scroll G f) (J:Cash W s μ L Q o C T (bend R u)): sprout H u i ∈ A:= by
      have hp : Kept J U (weightLog J i):= (logTest J i).mono (hU)
      exact ⟨hp.links,hp.borel,hp.rotate,hp.clutch⟩
   let Q0:= sprout H y i; let Q1:= sprout H (y+t) i; have hv' := h _ (Q' p); have hu := h _ (Q' p'); rw [hp,zero_smul,add_zero] at hv'; rw [hv,one_smul] at hu
   have he (x:Iota): sprout H (y + w x • t) i=Q0 + w x ^ 1 • (Q1-Q0):=(sprout_along H _ _ _ _).trans (by rw [pow_one]); rw[funext he]
   exact (Filled.steady Q0 hv').adds (Filled.shoots 1 le_rfl _ (A.sub_mem hu hv'))
variable (w:Iota→ℝ)(m m':Iota)(hm:w m=0)(hm':w m'=1)
   (y t:Reel.Scroll G f)(Q':∀ i:Iota,Cash W s μ L Q o C T (bend R (y+w i • t)))
local notation "Ω" => (fun i:Iota=> y+w i • t)
include hm hm' Q'
lemma terms_filled (p:H.ThinP)(Y:Support c)(hY:H.smallAt p ⊆ Y)(q:Paint p.val n)(he:chooseSlot q≠ Candle.perch n):
     Filled (Pop H Y) (inserts q) w (fun j=> press H (Ω j) q):= by
   let A:= Pop H Y; let f (j:Iota) := press H (Ω j) q; let h i j:= sprout H (Ω j) (i:↥(logs p.val)).val; let k i:= Series.rank (q i)
   let Z i:= ((k i).factorial:ℝ)⁻¹; let v i j:= Z i • (h i j ^ k i)
   have hv i: Filled A (k i) w (v i):= by
      have hz : H.supportP (identityLog i.val) ⊆ Y:= (subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans hY
      have hc := (sprout_filled H w m m' hm hm' y t Q' _ hz).power (P:=A) (k i) (Kept.fixed 1) (fun _ hx _ hy => Kept.times hx hy) (popPow H)
      rw [one_mul] at hc; exact hc.scaling (Z i)
   have ht : f=∏ i,v i:= by
     ext x F X g; unfold f; rw [Finset.prod_apply]; simp_rw [Finset.prod_apply]; apply prod_congr rfl; intro i _; rw [Candle.noOvercharge he]; change _ = ((k i).factorial:ℝ)⁻¹*(h i x F X g)^k i; rw [div_eq_mul_inv]; exact mul_comm ..
   change Filled A (∑ i,k i) w f; rw [ht]; exact Filled.accumulate _ _ _ (fun i _=> hv i) (Kept.fixed 1) (fun _ hx _ hy=>Kept.times hx hy) (popPow H)
variable {b' t₀ u σ e d r B δ : ℝ}{k l:ℕ} (N: Captain H k b' t₀ u σ e d r B δ l χ)
include N
lemma team_filled (p:H.ThinP)(V:Config G c)(hv: Healthy (Pressure.temp s) (H.smallAt p) V)(q:Orders n)(he:q.val ≤ n) : Filled ⊤ q.val w (fun j=> memo V (team H (Ω j) (χ:=χ) p q)):= by
   by_cases h:live H p
   swap; · simp_rw [Reel.short H _ _ _ h]; exact Filled.steady _ Submodule.mem_top
   let Z:= Finset.univ.filter fun i:Paint p.val n=> chooseSlot i=q
   let g (i:Paint p.val n) j:= episode H χ p.val (press H (Ω j) i)
   have hh (i:Paint p.val n) (hi:i∈Z):= mem_filter.mp hi|>.2
   have hz j:team H (Ω j) (χ:=χ) p q=∑ i∈ Z,g i j:= by ext; rw [team,if_pos h,Finset.sum_apply]; rfl
   simp_rw [hz,map_sum]; convert! Filled.group (P:=⊤) (w:=w) (n:=q.val) Z (fun i j=>memo V (g i j)) ?h using 1; swap
   · intro i hi; have h':chooseSlot i ≠ Candle.perch n:=by rw [hh _ hi]; intro h; rw [h] at he; change n+1 ≤ n at he; omega
     have ht : inserts i ≤ q.val:=by
       have hq : min (n+1) (inserts i)=q.val := congr_arg Fin.val (hh i hi)
       omega
     exact (pendulum N V hv p.2.2 (terms_filled H w m m' hm hm' y t Q' p _ (subset_refl _) i h')).onward ht
   ext1 j; simp only [Finset.sum_apply]
end YM.LocalTaylorR2.Reel
