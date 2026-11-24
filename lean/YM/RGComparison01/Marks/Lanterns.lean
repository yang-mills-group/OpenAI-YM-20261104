import YM.RGComparison01.Marks.Kinsman
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
    (L':Relay (A:=A) (D:=D) hC he Z)
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {E : Tree.Forest (stepped Q h).ratio} {E' : Tree.Forest (stepped Q H).ratio}
variable (x : Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (p : Cabinet.Folder χ)
    (hS:A.garden p⊆neighbors n x)
local notation "q" => (A.shell p)
local notation "U₁" => (D.shell (send Z p))
open PhysicalNext.Repeat.Lotus Team Merge Palette Switch Pledge Pillow
variable {σ:Type} (M₀:σ→ Leaf R)(M₁:σ→ Leaf R')
-- census movie specs before moments
structure Veils (t:σ→ χ) (x:Site C) (n:ℕ) : Prop where
   grant : Relay (A:=A) (D:=D) hC he Z
   atA (i:σ) : A.ink (t i)= Palette.sign M₁ (stepped Q H) i
   sight (i:σ) : D.ink (Z (t i))= Palette.sign M₀ (stepped Q h) i
   forward : ∀ i, separation x (A.site (t i)) ≤ n
   motion {E : Forest (stepped Q h).ratio} {F' : Forest (stepped Q H).ratio}
      {C₁:Coat T E} {C₂:Coat T' F'} (J: Stellar hC he K s C₁ C₂) (u : Air f G)(i:σ):
         (M₁ i).paidU C₂ o.a (C₂.liftA R'.beta (Stellar.blow (Lace.project (h:=h) (H:=H) hC he) u))=(M₀ i).paidU C₁ o.a (C₁.liftA R.beta u)

namespace Veils
variable {M₀ M₁}{t:σ→χ} (Z' : Veils (hC:=hC) (he:=he) (A:=A) (D:=D) (Z:=Z) M₀ M₁ t x n)
local notation "X₀"=> Pillow.Tags M₀ («S»:=S)
local notation "X₁"=> Pillow.Tags M₁ («S»:=Y)
include Z' hZ
lemma unique (i j:σ) : Palette.sign M₁ (Y) i=Palette.sign M₁ Y j ↔ Palette.sign M₀ (S) i=Palette.sign M₀ (S) j:= by
   rw [← Z'.atA,←Z'.atA,←Z'.sight,←Z'.sight]; exact ⟨fun hv=>congr_arg _ (congr_arg Z (A.ink.injective hv)),fun hv=> congr_arg _ (Z'.grant.lift.point (by omega) _ _ _ (Z'.forward i) (Z'.forward j) (D.ink.injective hv))⟩
def slope : X₁≃ X₀ :=
    ⟨fun i=> ⟨i.val,fun j hj k hk h=> i.2 hj hk ((Z'.unique x n hZ j k).2 h)⟩,fun i=>⟨i.val,fun j hj k hk h=> i.2 hj hk ((Z'.unique x n hZ j k).1 h)⟩,fun _=> rfl,fun _=>rfl⟩
local notation "Jt"=> Z'.slope x n hZ
variable (F' : Pillow.Tags M₁ («S»:=stepped Q H))
include hS
lemma acrossReach : (F'.reach⊆q)↔((Jt F').reach⊆ U₁):= by
   constructor
   · intro h i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi
     have hp : t j ∈ p:= by obtain ⟨x,hx,hX⟩:=mem_map.mp (h (F'.reaches_of hj)); exact A.ink.injective (hX.trans (Z'.atA j).symm) ▸ hx
     change Palette.sign M₀ S _∈ U₁; rw [← Z'.sight]; exact mem_map_of_mem _ (mem_image_of_mem Z hp)
   intro h i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; rw [← Z'.atA]; obtain ⟨k,hk,h₀⟩:= mem_map.mp (h ((Jt F').reaches_of (show j∈ (Jt F').val from hj))); obtain ⟨s,hs,rfl⟩:= mem_image.mp hk; have hp:= D.ink.injective (h₀.trans (Z'.sight j).symm)
   exact mem_map_of_mem _ ((Z'.grant.lift.point (by omega) x _ _ ((neighbors_mem ..).1 (hS (A.spot p s hs))) (Z'.forward j) hp) ▸ hs)
-- Residual unannotated factors pull back
lemma remains (hv:F'.reach ⊆ q) :
    let P:= p\(F'.val.image t); q\(team M₁ F').signs Y=A.shell P∧ U₁\(team M₀ (Jt F')).signs S=D.shell (send Z P):=by
   intro P'
   let V:=F'.val.image t; have hx:A.shell V=F'.reach:= by
      unfold Cabinet.shell V Tickets.reach; rw [Finset.map_eq_image,Finset.image_image,show A.ink ∘ t=Palette.sign M₁ Y from funext fun i=> Z'.atA i]
   have ht : V⊆p:=by intro i hi; obtain ⟨z,hz,hK⟩:=mem_map.mp (hv (hx ▸ (show A.ink i∈A.shell V from mem_map_of_mem A.ink hi))); exact A.ink.injective hK ▸ hz
   have he : D.shell (send Z V)=(Jt F').reach:= by
     unfold Cabinet.shell send V Tickets.reach; simp_rw [Finset.map_eq_image,Finset.image_image]; change F'.val.image _=F'.val.image _; exact image_congr fun i _=> Z'.sight i
   rw [Palette.label,Palette.label,← hx,← he,← show (A.shell _)= A.shell p \ A.shell V from Finset.map_sdiff ..,← show D.shell _=_ from (show ((send Z p \ send Z V).map D.ink)=_ from Finset.map_sdiff ..)]; refine ⟨rfl,congr_arg _ ?_⟩
   exact Eq.symm (Finset.image_sdiff_of_injOn (Z'.grant.injected x _ (by omega) _ hS) ht)
lemma film {Θ : Coat T E} {Θ' : Coat T' E'} (J : Stellar hC he K s Θ Θ') (k k':Finset ℕ) (hv:F'.reach ⊆ q) (u : Air f G):
    (team M₁ F').premium Θ' W o.a X.table k' X.halo (Stellar.blow (L) u) q = (team M₀ (Jt F')).premium Θ W o.a X.table k X.halo u U₁ := by
   let z:=Jt F'; let v:=(team M₁ F').signs Y; let w:=(team M₀ z).signs S
   have hP : v⊆q:= by rw [show v=_ from Palette.label ..]; exact hv
   have h' : w⊆U₁:= by rw [show w=_ from Palette.label ..]; exact (acrossReach x n hZ p hS Z' F').1 hv
   unfold Team.premium; rw [if_pos hP,if_pos h']; apply congr_arg₂ HMul.hMul
   · have h₀ : Set.InjOn M₀ z.val:= fun i hi j hj h=> z.prop hi hj (show Palette.sign M₀ S i=Palette.sign M₀ S j from congr_arg (fun k:Leaf R=> k.turn.badge S) h)
     have h₁ : Set.InjOn M₁ F'.val:= fun i hi j hj h=> F'.prop hi hj (show Palette.sign M₁ Y i=Palette.sign M₁ Y j from congr_arg (fun k:Leaf R'=> k.turn.badge Y) h)
     change (∏ j∈ F'.val.image M₁,j.paidU _ _ _)= (∏ j∈z.val.image M₀,j.paidU _ _ _); rw [Finset.prod_image h₁,Finset.prod_image h₀]; exact Finset.prod_congr rfl fun i _=> Z'.motion J u i
   obtain ⟨hx,he⟩:= remains x n hZ p hS Z' F' hv; rw [hx,he]; unfold Coat.term Cabinet.shell; rw [prod_map,prod_map]; unfold send; rw [prod_image ((Z'.grant.injected x _ (by omega) _ hS).mono (coe_subset.mpr sdiff_subset))]; exact Finset.prod_congr rfl (fun i hi=> (Z'.grant.grant J _ _ u i))
end Veils
end YM.RGComparison01.Relay
