import YM.FVA1.Loans

/-! Fixed-arity polynomial calculation supplied to the public interface.
Does not identify `cards` (which uses actual fragrances & booking/thermal
power/order) with the independent formal calculation. -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent MenuBridge
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {T I J V:Type}[Fintype I][Fintype V][Nonempty V][DecidableEq V]
variable {G:Gauge}{n m:Side}{Γ:Census V}{A:RG.Rep G n}
variable (q:I→ Menu.Hat Γ A)(read:I→(V→T)→ℂ)
variable (T':StepData m n)
def project (u:Positions V n):Positions V m where
  origin := T'.ratio.parent ∘ u.origin
  stub i:= Finset.image T'.ratio.parent (u.stub i)
  mem i:=mem_image_of_mem _ (u.mem i)

set_option quotPrecheck false
local notation "Y"=> Menu.Mound q
local notation "χ" => Menu.heap q
variable (header : V→(V→T)→ℂ)(st : ℕ → Prop)(σ w:V→ℝ)
local notation "M!"=> fun i=>(χ i).s
-- Stocks over V-free alphabet but funded in σ or w.
variable (E:RG.Rep G m)(D D' D₀ : Stock (n:=m) (Menu.Mound q) J G) (o:Positions V n)
-- shares check
structure Coil (J:Type) {V:Type}[DecidableEq V](T:Type)(Γ:Census V) (R:RG.Rep G m) where
  whole : Film J T Γ R
  model : Film J T Γ R
  tail : Film J T Γ R

namespace Coil
variable {c:Side}{R:RG.Rep G c}
structure Checks (D:Coil J T Γ R)(φ:V→(V→T)→ℂ)(x:Positions V c):Prop where
   ports : D.whole.tape=x ∧ D.model.tape=x ∧ D.tail.tape=x
   units : D.whole.header=φ ∧ D.model.header=φ ∧ D.tail.header=0
   support : D.model.surround=D.whole.surround ∧ D.tail.surround=D.whole.surround
   merged : D.whole.soft=D.model.soft+D.tail.soft
   gas : D.whole.gas=D.model.gas ∧ D.whole.gas=D.tail.gas
structure Invoice [AddCommGroup T][Module ℂ T] (D:Coil J T Γ R)(C:Controls V T)(w:V→ℝ)(s h a k b κ:ℝ):Prop where
   format : D.whole.Fit ∧ D.model.Fit ∧ D.tail.Fit
   dossier : D.whole.Pays C w s h a k κ
   marks : D.model.Pays C w s h a k κ ∧ D.tail.Pays C w s 0 b k κ
end Coil

def wind (D D' D₀: Stock (n:=m) (Menu.Mound q) J G) : Coil J T Γ E where
  whole := D.reinsert E (M!) (clipTest q read σ) (project T' o) header
  model := D'.reinsert E (M!) (clipTest q read σ) (project T' o) header
  tail := D₀.reinsert E (M!) (clipTest q read σ) (project T' o) 0

local notation "B"=> wind q read T' header σ E o D D' D₀
variable {s h g x c:ℝ}
structure Ran (S:StepData m n) (E:RG.Rep G m)(D D' D₀: Stock (n:=m) (Menu.Mound q) J G)(σ:V→ℝ) (a b v s:ℝ):Prop where
  equations : S.push A.beta (counts0 q σ S) = D.density0 E -- use S! not S
  laws : S.IsKernel A.beta G
  priced : ∃ h b v d e:ℝ,A.Lawful h b v d e
  theUnits : D.Room E ∧ D'.Room E∧ D₀.Room E
  supports : D.X=D'.X ∧ D'.X=D₀.X ∧ D.requires=D'.requires ∧ D'.requires=D₀.requires
  recurs (i z) : D.bin i z = D'.bin i z+D₀.bin i z
  forcers : D.hard=D'.hard ∧ D.hard=D₀.hard
  region : D.requires = fun i=> (Menu.heap q i).M.crest.image S.ratio.parent
  cost : D.Lent E (1: Menu.Mound q→ℝ) s a v ∧ D'.Lent E (1: Menu.Mound q→ℝ) s a v ∧ D₀.Lent E (1: Menu.Mound q→ℝ) s b v

local notation "λ0" P => Stock.reinsert P E (M!) (clipTest q read σ) (project T' o)
omit [Fintype V] [Nonempty V] in
lemma coiling {a b v s}
    (h:Ran q T' E D D' D₀ σ a b v s) : (B).Checks header (project T' o) :=by
    refine ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨h.supports.1.symm,(h.supports.1.trans h.supports.2.1).symm⟩,?_ ,?_⟩
    · change (fun x i=>decSum _ _ (D.bin i) x) = _; funext x i j U
      have hx (D1:Stock (n:=m) (Menu.Mound q) J G) (f): (Stock.reinsert D1 E (M!) (clipTest q read σ) (project T' o) f).soft x i j U= ∑ k, (decMode (M!) (fun k=> (clipTest q read σ) k x) k.val j)*(D1.bin i k U):=by
        change (∑ k, (decMode (M!) (fun k=> (clipTest q read σ) k x) k.val j) • (D1.bin i k)) U =∑ k, (decMode (M!) (fun k=> (clipTest q read σ) k x) k.val j)*(D1.bin i k U)
        simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      change (Stock.reinsert D E (M!) (clipTest q read σ) (project T' o) header).soft x i j U= _ + _
      simp [wind,hx, ←sum_add_distrib,h.recurs i,mul_add]
    rcases h.forcers with ⟨h1,h2⟩; unfold wind Stock.reinsert; simp only [h1,h1.symm.trans h2, and_self_iff]

variable [AddCommGroup T][Module ℂ T]
omit [Nonempty V] in
lemma consumeRan {a b v s h k κ:ℝ}
    (hr:Ran q T' E D D' D₀ σ a b v s) (C:Controls V T) (he:∀ i,0<σ i) (hl:∀ i,SlotLinear (q i).s.val (read i))(hT:∀ i,SlotLinear ({i}:Finset V) (header i))(hq:∀ i x,C.Admits x→‖read i x‖≤ 1)
    (hm:∀ i x,C.Admits x→σ i*‖header i x‖≤h)(hp:∀ i,∀ j∈(q i).s.val,o.stub j ⊆ (q i).M.crest)(hd:0<κ)(hb:v≤k*κ):
    (B).Invoice C σ s h a k b κ∧ ∀ φ:V→T, T'.push A.beta (offered q read header φ) = (B).whole.density φ:=by
    let z:=clipTest q read σ
    let u:=project T' o
    let a₀ (i:Y):= (Poly.toll σ ((M!) i))⁻¹
    have hs(k:Y): ∀ i∈ (χ k).s.val,o.stub i ⊆ (χ k).M.crest:=summed_stub q k o hp
    have hU(i):0 ≤ a₀ i:=inv_nonneg.mpr (Poly.worth he _).le
    have hz (i:Y): SlotLinear (χ i).s.val (z i):= clipLinear q read σ i hl
    have hA(i φ)(hx:C.Admits φ): ‖z i φ‖≤ a₀ i:= MenuBridge.clip_limit q read σ he φ (fun i=> hq _ _ hx) i
    have hP(i:Y): Poly.toll σ (χ i).s * a₀ i ≤ (1:Menu.Mound q→ℝ) i:= (mul_inv_cancel₀ (Poly.worth he _).ne').le
    rcases hr.cost with ⟨h1,h2,h3⟩; rcases hr.theUnits with ⟨hx,hy,hw⟩
    have cert (d:Stock (n:=m) (Menu.Mound q) J G)(φ e r)(h:d.Room E)(hW:d.Lent E (1:Y→ℝ) s r v)(hF:∀ i,SlotLinear ({i}:Finset V) (φ i))(hM:∀ i x,C.Admits x→σ i*‖φ i x‖≤e)
      (hk:d.requires=D.requires): let D':=d.reinsert E (fun i:Y=>(χ i).s) z u φ; D'.Fit∧D'.Pays C σ s e r k κ:=by
         intro D'; refine ⟨d.fit_reinsert E _ _ _ _ (fun i=>(χ i).shiny) h ?_ hz hF hW,d.pays_reinsert E _ _ _ _ h hW C _ hU hA _ he hP hM hd hb⟩
         intro i j hj; rw [hk,hr.region]; exact Finset.image_subset_image (hs _ _ hj)
    have hQ:=cert D header _ _ hx h1 hT hm rfl; have hQ':=cert D' header _ _ hy h2 hT hm hr.supports.2.2.1.symm; have hK:=cert D₀ 0 0 _ hw h3 (fun i=> SlotLinear.zero _) (fun i x _=>by change σ _ * ‖(0:ℂ)‖ ≤_; simp) (hr.supports.2.2.2.symm.trans hr.supports.2.2.1.symm)
    refine ⟨⟨⟨hQ.1,hQ'.1,hK.1⟩,hQ.2,hQ'.2,hK.2⟩,?_⟩; intro φ
    obtain ⟨o,c,b,f,t,HX⟩:=hr.priced
    rw [MenuBridge.forwarded q read σ he T' HX hr.laws,hr.equations]; funext U; exact (D.exact_reinsert E _ _ _ _ (fun i=>(χ i).shiny) _ _ hx h1).symm

end YM.FVA1
