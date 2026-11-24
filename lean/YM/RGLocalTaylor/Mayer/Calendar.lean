import YM.RGLocalTaylor.Mayer.Full
import YM.RG12.Burst.Wardrobe
/-!
# Register at the actual supported calendar

One request funds customer-side analytic Taylor estimates ALL orders registered
before this scale (arbitrarily many at full physical cutoff). Allows one to
strengthen the `bar`/later resets or combine other requests BEFORE constructing
a witness. Not a claim for any threshold choices different from the resulting
clock's.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Trees
open PhysicalNext.Repeat.Daisy.Charity.RG12

namespace Mayer
variable {M : ℕ} {θ K : ℝ}

def height : ℝ := 7/16

def arcRadius (G : Gauge) (L : Side) (x : ℝ) : ℝ := betaF G x L ^ height
lemma rate0 (G : Gauge) (L : Side) (a : ℝ) (f : ℝ→ℝ) (hf : Rate G L a f) (δ : ℝ) :
    Rate G L a (fun x=> degreePrice (radiusB x) (f x) δ):= degree10 L f hf δ

-- scalar occupation scaling and seal/moment etc. Uniform before side/draw.
lemma first_rates (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (Γ : Target.Expense Q) (hw: Γ.wanting ≤ -(7/16:ℝ))
    (j l M D : ℕ) {θ K μ δ : ℝ} (hμ:0<μ) (hK : Approved K θ j M)
    {u f α : ℝ→ℝ} (hu:Rate G L 0 u) (hf:Rate G L 0 f) (hr:Rate G L 0 α) (cost : ℝ) :
    let p := arcRadius G L
    let z x:= parentFee Q L μ x (u x) θ (f x) (p x) (α x) j l M
    ∀ᶠ x in atTop, 1≤p x ∧
      Q.goal L x ≤ K ∧ p x * Q.goal L x ≤ 1 ∧ (betaF G x L ^ (-(↑(M+1:ℕ)):ℝ) ≤ (p x ^ (M+1))⁻¹) ∧
      Real.exp (- Q.mark L μ x) ≤ (p x^(M+1))⁻¹ ∧
      degreePrice (radiusB x) (spreadRate M θ (p x) * (Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2 ∧
      degreePrice (radiusB x) (z x) δ ≤ 1/2 ∧ cost * (collars G δ x j D * (z x * (1-1/2)⁻¹)) ≤ 1 := by
  intro p z; let y:= fun x=> betaF G x L; let a:= Mayer.height
  have hs : 0≤a:=by norm_num [a,height]
  have ht : a+Q.rate<0:= by unfold a Mayer.height; linarith [Γ.reach]
  let t x:= spreadRate M θ (p x); have hP : Rate G L a p:=Rate.power; have ht' : Rate G L a t := (hP.mul_left θ).mul_left _
  have hR: Rate G L (a+Q.rate) (fun x=> t x * (Q.costs L μ 1 x 0).rootHit):=ht'.mul (Q.rate_root L hμ)
  have hF: Rate G L (a+Q.rate) (fun x=> firstLayer Q L μ x (l+j) (t x)):=by
    simpa only [firstLayer,Reserves.treeYield,pow_zero,mul_one] using! ((hR.mul_right (1-1/2)⁻¹).mul_left (Reserves.extract Q.ε (l+j) 0 0))
  have hg : Rate G L Q.rate (Q.goal L) := Rate.power
  have hJ: Rate G L 0 (fun x=> speedBill (f x) (u x) (α x) j):= by
    simpa only [zero_mul,zero_add] using! hf.mul ((((Rate.const 1).add hu).add (hr.mul_left 2)).pow j)
  have hz: Rate G L (a+Q.rate) z:= (hg.weaken (le_add_of_nonneg_left hs)).add (by
    simpa only [zero_add] using! ((hJ.mul_left ((2^j:ℝ)* ↑(M+2:ℕ))).mul hF))
  have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hp : Rate G L 0 (fun x=>collars G δ x j D):=by simpa only [zero_mul] using! ((he.pow (D*j)).mul_right (Reserves.polyPrice δ (D*j)))
  have hu := hp.mul (hz.mul_right (1-1/2)⁻¹) |>.mul_left cost
  have hW : Rate G L (-1-a*↑(M+1:ℕ)) (fun x=> Real.exp (-Q.mark L μ x)):=by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith only [hμ]) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x; dsimp only; rw [Real.rpow_two]; change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  filter_upwards [(rate0 G L _ _ hR Q.δ).below ht (1/2) (by norm_num), (rate0 G L _ z hz δ).below ht (1/2) (by norm_num),hu.below (by rw [zero_add]; exact ht) 1 zero_lt_one,hg.below Q.stop _ hK.pos,(hP.mul hg).below ht 1 zero_lt_one,hW (-a*↑(M+1:ℕ)) (by linarith), (Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hy ht hp hf ha hY
  have hi:y x≥0:= zero_le_one.trans hY
  have he : (p x^(M+1))⁻¹= y x ^ (-a*↑(M+1:ℕ)):= by unfold p arcRadius; rw [← inv_pow,← Real.rpow_neg hi]; rw [Real.rpow_mul_natCast hi (-a)]
  have hr' : a≤1:=by norm_num [a,height]
  rw [he]
  exact ⟨Real.one_le_rpow hY hs,(le_abs_self _).trans hp,(le_abs_self _).trans hf,Real.rpow_le_rpow_of_exponent_le hY (by nlinarith [Nat.cast_nonneg (α:=ℝ) (M+1)]), (le_abs_self _).trans ha,(le_abs_self _).trans hx,(le_abs_self _).trans hy,(le_abs_self _).trans ht⟩

/-- The last field also licenses its expenditure after `turnFee` etc. This
polygonal cost includes arbitrary finite derivative orders of root clocks.
Not a currency on a sum of unmasked quotient point evaluations. -/
def Passport (H : Cash W s μ L Q o C T R) (a w cost : ℝ) (δ : ℝ) (j power M : ℕ) : Prop :=
  let p := arcRadius G L s
  ∃ (A a' C d v t r B q e K θ uJ vJ : ℝ) (k l: ℕ) (N:Captain H j C d v t A a' r B q (l+j) Chi.canonical),
    Q.goal L s ≤ K ∧ Approved K θ j M ∧ Awning H N.conduit A a' (betaF G s L ^ (-(↑(M+1:ℕ)):ℝ)) e uJ vJ k l ∧
      Prepared N l M e uJ θ p ((M+4:ℝ)*r) a w δ ∧ cost * (collars G δ s j power*(w*(1-1/2)⁻¹)) ≤ 1

-- Chronological quantifiers. Existence before all steps and carriers.
def Passes (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (Γ : Target.Expense Q) (L : Side)
    (W μ : ℝ) (o: Target.Order G W) (D:RG.Stage) (i:ℕ) (x:ℝ) :=
  ∀ M ≤ i, ∃ w:ℝ,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ (R:RG.Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R),
      Passport H Γ.earn w (Height.away D) (Height.asset Γ) D.order D.power M

lemma passes (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (Γ : Target.Expense Q) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ W μ o D i,
    Γ.wanting ≤ -(7/16:ℝ) → 0<W → 0<μ → ∀ᶠ x:ℝ in atTop, Passes P Q Γ L W μ o D i x := by
  obtain ⟨n,h⟩:= Awning.available P Q
  refine ⟨n,fun L hL W μ o σ i hw hW hμ=>?_⟩
  let A x M w:= ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ (R:RG.Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R), Passport H Γ.earn w (Height.away σ) (Height.asset Γ) σ.order σ.power M
  suffices H : ∀ (M:ℕ),∀ᶠ x in atTop,∃ v,A x M v from (eventually_all.mpr (fun M:Fin (i+1)=> H M)).mono
    (fun x hx z hz=> hx (⟨z,Nat.lt_succ_of_le hz⟩:Fin (i+1)))
  intro M
  by_cases ht:∃ D:Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
  swap; · exact Eventually.of_forall fun x=> ⟨0,fun c f S T _ R C H=> let h:=H.laws.data.funds; False.elim (ht ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)⟩
  obtain ⟨D,hd,hL',hD⟩:=ht
  obtain ⟨a,b,C,q,r,e,uJ,vJ,v,w,t,B,k,l,hr,he,hu,hV,_,hX⟩:= h L hL (M+1) D hd σ.order Chi.canonical W hW μ hμ o
  let η:=Height.asset Γ; let α x:= (M+4:ℝ)*r x; let ρ := arcRadius G L
  obtain ⟨K,θ,hK⟩:= approved σ.order M; let z x:= parentFee Q L μ x (uJ x) θ (e x) (ρ x) (α x) σ.order l M
  filter_upwards [hX,first_rates (δ:=η) P Q L Γ hw σ.order l M σ.power hμ hK hu he (f:=e) (show Rate G L 0 α from hr.mul_left _) (Height.away σ)] with x hx hf
  refine ⟨z x,fun c f S T h R C' H=>?_⟩
  obtain ⟨N,hS⟩:= hx c f S T ((H.laws.data.funds).patch hL' hD) h R C' H
  have hP : Γ.earn+η+η≤ Q.exp:=by unfold η Height.asset; linarith
  have hA':1 ≤ α x:= one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) M]) N.conduit.active
  obtain ⟨hT,hs,ha,hg,hκ,hU,hB,hJ⟩:=hf
  exact ⟨_,_,_,_,_,_,_,_,_,_,K,θ,_,_,_,_,N,hs,hK,hS, purchased hS hK hs ha hA' le_rfl hT hg hκ hU hB (Height.asset_pos Γ) hP,hJ⟩

def decal (G : Gauge) : Decal G:= ⟨Passes,passes⟩
end Mayer
end YM.RGLocalTaylor
