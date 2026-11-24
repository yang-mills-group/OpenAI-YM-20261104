import YM.RG12.Burst.Wardrobe
import YM.RG12.Burst.Axes
import YM.RG12.Burst.Birch
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
open Mallow
open Push.SectorMeasure
open PhysicalNext.Repeat.Height Blush.Burst10
-- all losses for our criterion eligible. post.To make precise table in receipts
def Attic11 (Q:ConnectedActivityE6.Target G P) (Γ:Target.Expense Q)(L:Side) (W μ:ℝ) (o:Target.Order G W) (D:RG.Stage) (p:ℕ) (x:ℝ) : Prop:=
   let s : ℝ:= betaF G x L^ height Q
   1≤ s ∧ 0< betaF G x L ∧ foam Q L ∧ Trees.degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2 ∧ Trees.degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ ≤1/2 ∧
    1≤ Height.grow G L x ∧ Height.grow G L x ≤ s ∧ s*Height.grow G L x ≤ Real.exp (Q.mark L μ x) ∧
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ R C (H :Cash W x μ L Q o C T R), ∃ (A a q d v t r B k E :ℝ) (n:ℕ), Bikes Q L μ x Γ.earn E B D.order n ∧ Trees.degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x s B D.order n) E≤1/2 ∧
      (∀ d ≤ p, 2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level d)*1)*(((L.val:ℝ)^d))*coin11 Q L μ x s B D.order n E D.power ≤ betaF G x L^(-(4/5):ℝ)) ∧ ∃ N : Captain H D.order q d v t A a r B k n Chi.canonical, Silica.Heavy N.conduit ∧ Herd H N.conduit A B n

lemma annex11 (Q:ConnectedActivityE6.Target G P) (Γ:Target.Expense Q) : ∃ n:ℕ,∀ L:Side,n ≤ L.val → ∀ W μ  o h i, Γ.wanting ≤ -(7/16:ℝ) →0<W → 0<μ → ∀ᶠ x in atTop, Attic11 Q Γ L W μ o h i x:=by
  obtain ⟨n,h⟩:= RG12Axes.rocketsC10 P Q; obtain ⟨m,hE⟩:= early Q
  refine ⟨max n m,fun L hx W μ o U i hw hW hM=>?_⟩
  set b:= height Q; have hb:7/16 < b:=by unfold b height; linarith [Γ.reach]
  have hB:b+Q.rate<0:=by unfold b height; linarith [Γ.reach]
  let s x:= betaF G x L^ height Q; have hR:Rate G L b s:=Rate.power
  have hf:=hE L ((le_max_right ..).trans hx)
  have hk:∀ᶠ x:ℝ in atTop, (1≤ s x)∧0<betaF G x L:= ((Work.E09.betaF_growth G L).eventually_ge_atTop 1).mono fun x hl=>⟨Real.one_le_rpow hl (by linarith:0≤b),zero_lt_one.trans_le hl⟩
  have help : ∀ᶠ x in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ R C (H :Cash W x μ L Q o C T R), ∃ (A a q d v t r B k E :ℝ) (n:ℕ), Bikes Q L μ x Γ.earn E B U.order n ∧ Trees.degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x (s x) B U.order n) E≤1/2 ∧
      (∀ d ≤ i, 2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level d)*1)*(((L.val:ℝ)^d))*coin11 Q L μ x (s x) B U.order n E U.power ≤ betaF G x L^(-(4/5):ℝ)) ∧ ∃ N : Captain H U.order q d v t A a r B k n Chi.canonical, Silica.Heavy N.conduit ∧ Herd H N.conduit A B n:=by

    by_cases he:∃ D:Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
    swap; · exact Eventually.of_forall fun x c f S T _ R C H=>let h:=H.laws.data.funds; False.elim (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
    obtain ⟨D,he,hL,hJ⟩:=he; obtain ⟨A,a,q,d,v,t,r,B,k,n',hp,-,hT⟩:= h L ((le_max_left ..).trans hx) D he U.order Chi.canonical W hW μ hM o
    let e :=(Q.exp-Γ.earn)/2; have he':0<e:=by unfold e; linarith [Γ.first,Γ.worth,Γ.second]
    have hy := ready10 Q L μ hM U.order n' B s hp hR (by linarith) hB e
    have hc : Rate G L (-(b+(3/8))) (fun x=> (Height.grow G L x)⁻¹*cash10 Q L μ x (s x) (B x) U.order n' e U.power 2):=by
      have hp:= paid10 Q L μ hM U.order n' U.power B (b:=b) hp (by linarith) 2 e
      have he : Rate G L (-(3/8)) (fun x=>(Height.grow G L x)⁻¹):=by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; exact (Real.rpow_neg hx.le _).symm
      convert! he.mul hp using 1; push_cast; ring
    have hl : Rate G L (-(b+(3/8))) (fun x=>coin11 Q L μ x (s x) (B x) U.order n' e U.power):=by
       apply Rate.congr hc; exact Eventually.of_forall (fun x=> by unfold cash10 coin11; dsimp only; rw [_root_.mul_inv_rev]; ring)
    have hm (k:ℕ):=(hl.mul_left (2*(Push.Local.readPrice (Next.Foundations.hol G) ((Labels.frames G).level k)*1)*(((L.val:ℝ)^k)))) (-(4/5):ℝ) (by linarith)
    filter_upwards [hT, stables L Q hM B he' (v:=Γ.earn) (by unfold e; linarith) Γ.price hp U.order n' U.power, hy,eventually_all.mpr (fun k:Fin (i+1)=> hm k)] with x hv hh hh' hz c f S T h' R C H
    exact ⟨A,a,q,d x,v x,t x,r x,B x,k x,e,n',hh.1,hh',fun k hk=>(le_abs_self _).trans (hz (⟨k,Nat.lt_succ_of_le hk⟩:Fin (i+1))), hv c f S T ((H.laws.data.funds).patch hL hJ) h' R C H⟩
  have he0: Rate G L (3/8) (fun x=> Height.grow G L x):=Rate.power
  have he1 : Rate G L (-1-b-3/8) (fun x=>Real.exp (-Q.mark L μ x)):=by
     simpa only [syrup,one_mul] using (Mallow.infuso (G:=G) L 1 (μ/4) 1 (by linarith) zero_lt_one (-1-b-3/8))
  have hs: Rate G L (-1) (fun x=>s x*Height.grow G L x* Real.exp (-Q.mark L μ x)):=by
     convert! ((hR.mul he0).mul he1) using 1; ring
  filter_upwards [ready10' Q L μ hM s hR hB,hk,help, (Work.E09.betaF_growth G L).eventually_ge_atTop 1, hs.below (by norm_num) _ zero_lt_one] with x he ht hh hp hz
  refine ⟨ht.1,ht.2,hf,he.1,he.2, Real.one_le_rpow hp (by norm_num), Real.rpow_le_rpow_of_exponent_le hp (by linarith:3/8 ≤ b), ?_,hh⟩
  have hl:= (le_abs_self _).trans hz
  change s x * Height.grow G L x * Real.exp (-Q.mark L μ x) ≤ 1 at hl
  rw [Real.exp_neg, ← div_eq_mul_inv] at hl; exact by simpa using ((div_le_iff₀ (Real.exp_pos _)).mp hl)

def garment11 (G : Gauge) : Decal G:=⟨fun _ Q Γ L W μ=>Attic11 Q Γ L W μ,fun _P Q Γ=>annex11 Q Γ⟩
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
