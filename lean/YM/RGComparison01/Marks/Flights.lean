import YM.RGComparison01.Marks.Piston
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Relay
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {c f C F L₀: Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC:C.val=c.val*M} {he : 2≤ c.val}
variable {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} {R : RG.Rep G f} {R':RG.Rep G F}
  {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b} {Z : χ → ι}

local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {E : Tree.Forest (stepped Q h).ratio} {E' : Tree.Forest (stepped Q H).ratio}
variable (x : Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (p : Cabinet.Folder χ)
    (hS:A.garden p⊆neighbors n x)

open PhysicalNext.Repeat.Lotus Merge Palette Pledge Pillow
namespace Veils
open Pledge Ink Season Stowe Baked March
variable {σ : Type}{M₀:σ→ Leaf R}{M₁:σ→ Leaf R'}{t:σ→χ} (Z' : Veils (hC:=hC) (he:=he) (A:=A) (D:=D) (Z:=Z) M₀ M₁ t x n)
-- compare two ledgers.Affinity
variable [Fintype σ]
variable (hm : 4*Cabinet.garage b ℓ<c.val)(hk : Cabinet.garage b ℓ≤ n)
   (J : A.Record ℓ) (hJ : x∈ A.ground J.val) (i : coatP M₁ I' A J)
local notation "Zp"=> Z'.grant.recycle hm x J hJ
set_option quotPrecheck false
local notation "Tp"=> Veils.slope x n hZ Z'
include hk
-- descendant's audited pollen with same set, even NONINJECTIVE forms outside recipe are absent
omit hk in
def haven : coatP M₁ I' A J≃ coatP M₀ I D Zp := Equiv.piCongrRight fun _=> Tp

include hJ
omit [Fintype σ] Z' in
lemma coming : ∀ y, A.garden (J.val.2 y)⊆neighbors n x:=fun _=> (A.within _ _).trans ((A.extent J x hJ).trans (fun _ hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hk)))
local notation "hp"=> (Z'.haven x n hZ hm J hJ)
local notation "T₀"=> ride M₀ I D Zp
local notation "T₁"=> ride M₁ I' A J
omit [Fintype σ] in
lemma stellar (z:Finset σ): struck M₁ I' z (T₁ i) ↔ struck M₀ I z (T₀ ((hp) i)):= by
   apply and_congr Iff.rfl; apply forall_congr'; intro a; exact Z'.acrossReach x n hZ _ (coming (b:=b) _ _ hk J hJ a) (i a)

variable (g:σ→ℝ) (hq : T'= re T) (V:Config G c) (κ:Chi) (hv : RG.flags (Pressure.temp s) V=∅)
local notation "V'" => (L).low.links V
include hq hv
omit [Fintype σ] in
lemma field (z:Finset σ)(ht:struck M₁ I' z (T₁ i)) : pottery M₁ g κ (T₁ i) (V') = pottery M₀ g κ (T₀ (hp i)) V:=by
   unfold pottery Gas.term; apply congr_arg₂ HDiv.hDiv _ rfl; apply congr_arg₂ HMul.hMul
   · have ht':= Z'.grant.constant J.val _ (show 2* Cabinet.garage b ℓ<c.val from (by omega)) x (A.extent J x hJ)
     exact (A.stars J).symm.trans (ht'.trans (D.stars Zp)) -- coefficient seam defeq? Function comp notation
   apply Finset.prod_congr rfl; intro y hi; apply congr_arg₂ HMul.hMul rfl
   exact Z'.skink x n hZ (J.val.2 y) (coming _ _ hk J hJ y) (i y) (ht.2 y) hq V κ hv (J.property.poses y) ((Zp).property.poses y)

-- rough equality only on protected lanes
omit hk hJ hq hv
include Z' hk hv hq hm hZ
set_option maxHeartbeats 450000 in
lemma burst (z:Finset σ) (w : σ) (hw:w∈z) (hw': x ∈ (M₁ w).crest.image (decreed H).parent)
    (hp': ((L).low.cut x ∈ (M₀ w).crest.image (decreed h).parent)):
    Stowe.ship M₁ g I' A ℓ k z (V') («χ»:=κ) = Stowe.ship M₀ g I D ℓ k z V («χ»:=κ) := by
   let f (p:Cabinet.Record A ℓ) :ℝ:= ∑ i: Stowe.coatP M₁ I' A p, if Stowe.struck M₁ I' z (ride M₁ I' A p i) then Pillow.pottery _ g κ (ride M₁ I' A p i) (V') else 0
   let F (p:Cabinet.Record D ℓ):ℝ:=∑ i:Stowe.coatP M₀ I D p,if struck M₀ I z (ride M₀ I D p i) then Pillow.pottery M₀ g κ (ride M₀ I D p i) V else 0
   have he₂ (p:Cabinet.Record A ℓ)(v: x∈ A.ground p.val) : f p=F (Z'.grant.recycle hm x p v):=by
      unfold f F; let L':= Z'.haven x n hZ hm p v; refine Fintype.sum_equiv L' _ _ (fun i=>?_); rw [propext (stellar x n hZ Z' hm hk p v i z)]; split; next he=> exact Z'.field x n hZ hm hk p v i g hq V κ hv z ((Z'.stellar x n hZ hm hk p v i z).2 he)
      rfl
   refine Eq.trans (mold M₁ g I' A ℓ k x z (V') hw hw') ((Relay.sum_prism Z'.grant hm x k (g:=f) (fun p hp' _=> he₂ p hp')).trans (mold M₀ g I D ℓ k _ z V hw hp').symm) -- shape
where
  mold {α:Type}{G:Gauge}{c f L₀ : Side}{Tgt:Teller G}{W s a U:ℝ}{b :ℕ}{Q:Target G Tgt}{o : Target.Order G W}{S':StepData c f}{T':Tube G S'}{R':RG.Rep G f}
      (M:σ→Leaf R')(g:σ→ℝ)(I':Cash W s a L₀ Q o U T' R')(D':Cabinet α I' b)(ℓ k:ℕ)(x:Site c)(z:Finset σ)(V:Config G c)
     {w:σ}(hw:w∈z)(hX:x∈(M w).crest.image S'.ratio.parent):
     Stowe.ship M g I' D' ℓ k z V («χ»:=κ)= ∑ p∈(D'.podium ℓ k).filter (fun i=> x∈D'.ground i.val), ∑ i:Stowe.coatP M I' D' p,if struck M I' z (ride M I' D' p i) then Pillow.pottery _ g κ (ride M I' D' p i) V else 0:= by
     let f (j:D'.Record ℓ) (i: Stowe.coatP M I' D' j):ℝ:= if struck M I' z (ride M I' D' j i) then Pillow.pottery M g κ (ride M I' D' j i) V else 0
     let W' j:= ∑ i:Stowe.coatP M I' D' j,f j i
     unfold Stowe.ship Stowe.ledger; rw [sum_filter,Stowe.header, Finset.sum_map]; let K:=D'.podium ℓ k; change (∑ i∈ K.sigma (fun _=>univ),f i.1 i.2)=∑ i∈ K.filter _,W' i
     rw [Finset.sum_sigma]
     symm; exact sum_subset (filter_subset ..) (fun i hi hp'=> sum_eq_zero (fun j _=> if_neg (fun hh=>hp' (mem_filter.mpr ⟨hi, Stowe.crest M I' z (ride M I' D' i j) hh w hw hX⟩))))
end Veils
end YM.RGComparison01.Relay
