import YM.RGLocalTaylor.Laminate.Land
import YM.RGLocalTaylor.Mayer.Calendar
/-!
# Same marker/analytic receipt on the actual Coupled stage

Acquire *all data before quoting the trajectory and the marker and physical
volumes*. Prices are uniform despite allowing additional order/post-stage
cost strengthening (e.g. before packing Slide). Adaptation of `Mayer.Calendar`
approval proof. No assertion of order-uniform hypothesis on perturbation.
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
namespace Laminate
open RG01.Survive Mayer Trees YM.Merge Palette
open Daisy.Charity.RG12

variable {M : ℕ} {θ K : ℝ}
lemma all_rates (Q : YM.ConnectedActivityE6.Target G P)(L:Side) (Γ:Target.Expense Q) (hw : Γ.wanting ≤ -(7/16:ℝ))
    (j l M D:ℕ)(cost:ℝ){θ K μ δ:ℝ}(hμ:0<μ)(_hK:Approved K θ j M)
    {α v K':ℝ→ℝ}(hα:Rate G L 0 α)(hv:Rate G L 0 v)(hF: Rate G L 0 K') :
    let ρ' := Mayer.arcRadius G L
    let R x:= Laminate.rent Q L μ x θ (ρ' x) (α x) (K' x) (v x) j M l
    ∀ᶠ x in atTop, degreePrice (radiusB x) (Laminate.width Q μ L x) Q.δ ≤1/2 ∧
      degreePrice (radiusB x) (Mayer.spreadRate M θ (ρ' x)*Laminate.width Q μ L x) Q.δ ≤1/2 ∧
      degreePrice (radiusB x) (R x) δ ≤1/2 ∧
      cost*(collars G δ x j D*(R x*(1-1/2)⁻¹))≤1 :=by
  intro p z; let a:= Mayer.height
  have hs : 0≤a:=by norm_num [a,Mayer.height]
  have ht : a+Q.rate<0:= by unfold a Mayer.height; linarith [Γ.reach]
  have hg : Rate G L Q.rate (Q.goal L) := Rate.power
  have hW : Rate G L Q.rate (Laminate.width Q μ L) := (Q.rate_root L hμ).add (hg.add (hg.mul_right _))
  let t x:= spreadRate M θ (p x); have hP : Rate G L a p:=Rate.power; have ht' : Rate G L a t := (hP.mul_left θ).mul_left _
  have hR: Rate G L (a+Q.rate) (fun x=> t x * Laminate.width Q μ L x):=ht'.mul hW
  have hk: Rate G L (a+Q.rate) (fun x=> Laminate.first_price Q L μ x (l+j) (t x)):=by
    simpa only [first_price,Reserves.treeYield,pow_zero,mul_one] using! ((hR.mul_right (1-1/2)⁻¹).mul_left (Reserves.extract Q.ε (l+j) 0 0))
  have hJ: Rate G L 0 (fun x=> speedBill (v x) (K' x) (α x) j):= by
    simpa only [zero_mul,zero_add] using! hv.mul ((((Rate.const 1).add hF).add (hα.mul_left 2)).pow j)
  have hz: Rate G L (a+Q.rate) z:= (hg.weaken (le_add_of_nonneg_left hs)).add (by
    simpa only [zero_add] using! (((hJ.mul_left (↑(M+2:ℕ):ℝ)).mul_left (2^j:ℝ)).mul hk))
  have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hp : Rate G L 0 (fun x=>collars G δ x j D):=by simpa only [zero_mul] using! ((he.pow (D*j)).mul_right (Reserves.polyPrice δ (D*j)))
  have hu := hp.mul (hz.mul_right (1-1/2)⁻¹) |>.mul_left cost
  filter_upwards [(Mayer.rate0 G L _ _ hR Q.δ).below ht (1/2) (by norm_num),(rate0 G L _ z hz δ).below ht (1/2) (by norm_num),hu.below (by rw [zero_add]; exact ht) 1 zero_lt_one,(rate0 G L _ _ hW Q.δ).below Q.stop (1/2) (by norm_num)] with x hx hy ht hz
  exact ⟨(le_abs_self _).trans hz,(le_abs_self _).trans hx,(le_abs_self _).trans hy,(le_abs_self _).trans ht⟩

variable {ρ discount θ K α uJ vJ e : ℝ} {p : Molecule S} {N : Captain H j C' d v Y A b r B q n χ}
structure Airs (N : Captain H j C' d v Y A b r B q n χ) (l M:ℕ) (e uJ θ ρ α a w η:ℝ) : Prop where
  scale : 1 ≤ ρ
  pricebook {ι: Type} [_F:Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ): Plot M' H rA → Ready H.smallAt (radiusB s) (offerBook M' rA N.conduit θ ρ α uJ e M l) (a+η) w η (1/2)
  plus (M':Team R) (i):0 ≤ invoice M' i N.conduit θ ρ α uJ e M l
  tells (M':Team R) (i:H.ThinP)(t:Orders M)(U:Config G c): Healthy (Pressure.temp s) (H.smallAt i) U → Ore U (column M' i.val H (χ:=χ) M t) v ((ρ^t.val)⁻¹*invoice M' i.val N.conduit θ ρ α uJ e M l) j

lemma authorize (h : Awning H N.conduit A b discount e uJ vJ k l) (he : Approved K θ j M)(hT:Q.goal L s≤K)(hw:ρ*Q.goal L s≤1)
    (hA:1≤α)(hρ:1≤ρ)(ht:(M+4:ℝ)*r≤α)(hu:vJ≤α)
    (hD : discount≤(ρ^(M+1))⁻¹)(hE: Real.exp (-Q.mark L μ s)≤ (ρ^(M+1))⁻¹)
    (hx : degreePrice (radiusB s) (Laminate.width Q μ L s) Q.δ ≤1/2)(hs:degreePrice (radiusB s) (Mayer.spreadRate M θ ρ *Laminate.width Q μ L s) Q.δ ≤1/2)
    (hq:a+η+η≤Q.exp)(hη:0<η)(hF:degreePrice (radiusB s) (Laminate.rent Q L μ s θ ρ α uJ e j M l) η≤1/2) : Airs N l M e uJ θ ρ α a (Laminate.rent Q L μ s θ ρ α uJ e j M l) η:=
  ⟨hρ,fun M' rA hP=> installed M' rA N.conduit hP h he hA hρ N rfl hx hs hq hη hF,fun M' p =>invoice_check M' p h he hρ hA,fun M' i t U h' => asked M' i.val h he hT hρ hw hA ht hu hD hE i.2.2 t U h'⟩

-- portable expense book. Aiming at all χ? canonical needed for Use.
def Known (H : Cash W s μ L Q o C T R) (a w cost η:ℝ)(j power M:ℕ): Prop :=
  let p:=Mayer.arcRadius G L s
  ∃ (A a' C d v t r B q e K θ uJ vJ:ℝ)(k l:ℕ)(N:Captain H j C d v t A a' r B q (l+j) Chi.canonical),
    Q.goal L s≤K ∧ Approved K θ j M ∧ Awning H N.conduit A a' (betaF G s L ^ (-(↑(M+1:ℕ)):ℝ)) e uJ vJ k l ∧ Airs N l M e uJ θ p ((M+4:ℝ)*r+vJ) a w η ∧
    cost*(collars G η s j power*(w*(1-1/2)⁻¹))≤1

def Needs (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (Γ : Target.Expense Q) (L : Side)
    (W μ : ℝ) (o: Target.Order G W) (D:RG.Stage) (i:ℕ) (x:ℝ) :=
  ∀ M ≤ i, ∃ w:ℝ, ∀ (c f:Side)(S:StepData c f)(T:Tube G S),Stamp T → ∀ (R:RG.Rep G f)(C:ℝ)(H:Cash W x μ L Q o C T R),
       Known H Γ.earn w 1 (PhysicalNext.Repeat.Height.asset Γ) D.order D.power M

lemma needs (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (Γ : Target.Expense Q) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ W μ o D i,
    Γ.wanting ≤ -(7/16:ℝ) → 0<W → 0<μ → ∀ᶠ x:ℝ in atTop, Needs P Q Γ L W μ o D i x := by
  obtain ⟨n,h⟩:= Awning.available P Q
  refine ⟨n,fun L hL W μ o σ i hw hW hμ=>?_⟩
  let Y x M w:= ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ (R:RG.Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R), Known H Γ.earn w 1 (Height.asset Γ) σ.order σ.power M
  suffices H : ∀ (M:ℕ),∀ᶠ x in atTop,∃ v,Y x M v from (eventually_all.mpr (fun M:Fin (i+1)=> H M)).mono
    (fun x hx z hz=> hx (⟨z,Nat.lt_succ_of_le hz⟩:Fin (i+1)))
  intro M
  by_cases ht:∃ D:Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
  swap; · exact Eventually.of_forall fun x=> ⟨0,fun c f S T _ R C H=> let h:=H.laws.data.funds; False.elim (ht ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)⟩
  obtain ⟨D,hd,hL',hD⟩:=ht
  obtain ⟨a,b,C,q,r,e,uJ,vJ,v,w,t,B,k,l,hr,he,hu,hV,_,hX⟩:= h L hL (M+1) D hd σ.order Chi.canonical W hW μ hμ o
  let η:=Height.asset Γ; let α x:= (M+4:ℝ)*r x+vJ x; let ρ := Mayer.arcRadius G L
  obtain ⟨K,θ,hK⟩:= Mayer.approved σ.order M; let z x:= Laminate.rent Q L μ x θ (ρ x) (α x) (uJ x) (e x) σ.order M l
  have hr':Rate G L 0 α:=(hr.mul_left _).add hV
  filter_upwards [hX,Mayer.first_rates (δ:=η) P Q L Γ hw σ.order l M σ.power hμ hK hu he hr' (Height.away σ),Laminate.all_rates Q L Γ hw σ.order l M σ.power 1 hμ hK (δ:=η) hr' (v:=e) he (K':=uJ) hu] with x hx hf hu
  refine ⟨z x,fun c f S T h R C' H=>?_⟩
  obtain ⟨N,hS⟩:= hx c f S T ((H.laws.data.funds).patch hL' hD) h R C' H
  have hP : Γ.earn+η+η≤ Q.exp:=by unfold η Height.asset; linarith
  have hD:1 ≤ (M+4:ℝ)*r x:= one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) M]) N.conduit.active
  have hA:1 ≤ α x:= hD.trans (le_add_of_nonneg_right hS.cSc); obtain ⟨hT,hs,ha,hg,hκ,-⟩:=hf
  exact ⟨_,_,_,_,_,_,_,_,_,_,K,θ,_,_,_,_,N,hs,hK,hS,authorize hS hK hs ha hA hT (le_add_of_nonneg_right hS.cSc) (le_add_of_nonneg_left (zero_le_one.trans hD)) hg hκ hu.1 hu.2.1 hP (Height.asset_pos Γ) hu.2.2.1,hu.2.2.2⟩

def lease (G:Gauge): Decal G:= ⟨Needs,needs⟩
end Laminate
end YM.RGLocalTaylor
