import YM.RG01Estimate.CompassMint
/-!
 # Entries in finite cutoff, unique and complete on crossed apertures. Any
 Countable indexing; underlying model provenance NOT supplied by this lemma. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {Γ : Type} {c f C F L'' : Side} {P:Patch}{M D' : ℕ}{K:Teller G}

variable {h : f.val=c.val*P.L.val}{H:F.val=C.val*P.L.val}{Q: KernelChoices}{hC:C.val=c.val*M}{he:2≤c.val} {p u w W v:ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T:Tube G (stepped Q h)}{T':Tube G (stepped Q H)}{R:RG.Rep G f}{R':RG.Rep G F}{V:Lex Γ f}{V': Lex Γ F}
    {X:ConnectedActivityE6.Target G K}{o:ConnectedActivityE6.Target.Order G W}
variable (hp:R'.path=R.path) (I : Cash W p u L'' X o v T R) (I' : Cash W p u L'' X o w T' R') (A: Charts (h:=h) (H:=H) hC he R R' V V')
   (x:Site C) {d Z m n:ℕ}
local notation "B" => radiusB p
local notation "p'" => optic X.halo B d
local notation "D" => house X.halo B d m
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
variable (hQ: StageMask R (stepped Q h) V d)(hW:StageMask R' (stepped Q H) V' d)(hZ:2*house X.halo (radiusB p) d m<c.val)
include hW hZ he
lemma picks (i j:Sons Γ C F) (hi:Admit I' V' m i)(hj:Admit I' V' m j)(ht:x∈arborX I' V' i)(hv:x∈arborX I' V' j) (hx:follows (L) i=follows (L) j) : i=j:= by
   have hu: i.fst=j.fst:= congr_arg (fun i:Sons Γ c f=> i.fst) hx; rcases i with ⟨v,i⟩; rcases j with ⟨u,j⟩; dsimp only at hu; subst u
   unfold follows at hx; injection hx with h' hT
   have h := sailing (Γ:=Γ) (hC:=hC) (hc:=he) (h:=h) (H:=H) Q
   have hf {p q:Sons Γ C F} {k} {l} (hp:Admit I' V' m p) (hq:Admit I' V' m q) (hs:x∈arborX I' V' p) (hb:x∈arborX I' V' q)
       (hv: (p.2 k).image (warps (L))=(q.2 l).image (warps (L))): p.2 k ⊆ q.2 l:=by
        intro a ha; obtain ⟨j,hj,hx⟩:= mem_image.mp (show warps (L) a∈ (q.2 l).image (warps (L)) from hv ▸ mem_image_of_mem (warps (L)) ha)
        have hm (p:Sons Γ C F) (h:Admit I' V' m p)(hp:x∈ arborX I' V' p) (k i)(hi:i∈p.2 k): separation x (aisle (Y) i)≤ (D):= (neighbors_mem ..).1 ((within I' V' m hW _ h hp) (patio I' V' p k (positioned I' V' m _ (h.hot k) hW _ hi))) -- edit
        exact (h.point hZ x j a (hm q hq hb l j hj) (hm p hp hs k a ha) hx) ▸ hj
   congr 1; funext k
   exact Finset.Subset.antisymm (hf (k:=k) (l:=k) hi hj ht hv (congr_fun hT k)) (hf (k:=k) (l:=k) hj hi hv ht (congr_fun hT k).symm)

omit hZ
include I I' A hp hQ
lemma return_leg (hc:2*n<c.val) (hs:D'+p'≤ n) (p:hall Γ c f)(ht:Kind I V m p)(hx:arbor I V p⊆ neighbors D' x') : ∃ q: hall Γ C F, Kind I' V' m q ∧ arbor I' V' q ⊆ neighbors n x ∧ q.image (warps (L))=p:= by
   let f:= warps (Γ:=Γ) (L); let Pq:=sailing (Γ:=Γ) (hC:=hC) (hc:=he) (h:=by assumption) (H:=H) Q
   choose Z hF hK using Pq.esc x
   let z:= p.image Z
   have hv i (hi:i∈p): separation x (aisle (Y) (Z i)) ≤ D':=(hK i).trans_le ((neighbors_mem ..).1 (hx (positioned I V m _ ht hQ _ hi)))
   have hu (i:Header Γ C F) (hi:i∈ z) : separation x (aisle (Y) i)≤ D' ∧ I'.supportP (mint Y V' i)⊆ neighbors n x:= by
       obtain ⟨i,hv',rfl⟩:= mem_image.mp hi
       have ht' := hv _ hv'; have hw := (recession hp I I' A (Z i)).1; rw [hF] at hw
       have hq:= location V' hW T' (show 0<B from lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) (Z i) (hw.trans_le (ht.vote _ hv')) (m:=X.halo)
       refine ⟨ht',fun j hk=>?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (aisle _ _) _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hq.2 hk))).trans hs)
   have he : arbor I' V' z⊆neighbors n x:= by
       rw [gardens]; intro i hi; obtain ⟨j,hj,hk⟩:=mem_biUnion.mp hi; exact (hu j hj).2 hk
   have ht' : z.image (warps (L))= p:= by unfold z; rw [image_image,show warps (L) ∘ Z=id from funext hF,image_id]
   have hh : Set.InjOn f (z: Set (Header Γ C F)):= fun i hi j hj hh=> Pq.point hc x i j ((hu i hi).1.trans (by omega)) ((hu j hj).1.trans (by omega)) hh
   exact ⟨z,(rolls hp I I' A z hh ((Meadow.garden hC x hc).mono (coe_subset.mpr he))).2 (ht' ▸ ht),he,ht'⟩

lemma patch (hc: 2*(D+p')<c.val)(p:Sons Γ c f)(hi:Admit I V m p) (ht:x'∈ arborX I V p) : ∃ q:Sons Γ C F, Admit I' V' m q ∧ x ∈ arborX I' V' q ∧ follows (L) q=p:= by
   choose Z hz hb he' using fun i=> return_leg hp I I' A x hQ hW hc le_rfl (p.2 i) (hi.hot i) ((patio I V p i).trans (within I V m hQ _ hi ht))
   let u:Sons Γ C F:= ⟨_,Z⟩; have h : follows (L) u=p:= congr_arg (Sigma.mk _) (funext he')
   have hk:arborX I' V' u⊆ neighbors (D+p') x:= by intro i hi; obtain ⟨j,hj,hv⟩:= mem_biUnion.mp hi; exact hb j hv
   have hh:= parity hp I I' A x hW u hz hc hk; rw [h] at hh
   refine ⟨u,⟨hi.count,hz,hh ▸ hi.glow⟩,?_,h⟩
   obtain ⟨i,hi,hq⟩:= mem_image.mp (show (L).low.cut x∈ (arborX I' V' u).image ((L).low.cut) from (by rw [← cross hp I I' A u,h]; exact ht))
   exact ((Meadow.garden hC x hc) (hk hi) (show x∈ neighbors (D+p') x from (neighbors_mem ..).2 (by simp)) hq) ▸ hi

end YM.RG01Estimate.Evoc
