import YM.MergeProof.Montage
import YM.OPE.Vitrines.Exhibit
/-! # Accumulate regular reserve; strengthening from MergeProof/Sonata. -/

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "c'" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
local notation "κ" => kappa H i
open Extra.Histories
set_option quotPrecheck false
section
variable {B H N p i Y} {x:Config G (H.S.side (i+1) p)→ℂ}{P:Coefficient F (H.S.side i p)}
    {q:ℝ}{v:F.Coeff}{a b t r:ℝ}
lemma Lucent.weaken (h:Lucent B H N p i Y x P v a b) (ht:a≤t)(hu:b≤r) : Lucent B H N p i Y x P v t r:= ⟨h.format,h.agrees,h.leadP.trans ht,by obtain ⟨u,t,hf,h₁⟩:=h.future; exact ⟨u,t,hf,h₁.trans hu⟩,(by obtain ⟨q,he,hz⟩:=h.pale; exact ⟨q,he,hz.trans hu⟩)⟩
lemma Lucent.bound (h:Lucent B H N p i Y x P v a b):P.remBound 0 Rout κ b:=by
   obtain ⟨u,t,hf,ht⟩:=h.future
   have he:1 ≤ turnCost (Rout).p.order (Rout).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ one_le_two))
   exact hf.bound ((add_le_add_left (le_mul_of_one_le_left hf.first he) t).trans ht)
lemma CreamBid.weaken {X:Wing→Prop} {Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}{s z:ℝ}{v':Res G (H.S.side (i+1) p)}{T:ℂ}
    {u:Config G (H.S.side (i+1) p)→ℂ} (h:CreamBid B H N p i Y x v' T Q X u v a b s)(hp:a≤t)(hq:b≤r)(hz:s≤z): CreamBid B H N p i Y x v' T Q X u v t r z:=by
    obtain ⟨P,hP,hR⟩:=h; exact ⟨P,hP.weaken hp hq,hR.climb le_rfl hz hq⟩
end
section
variable {ι:Type}[Nonempty ι][Countable ι]
  {f : ι → Config G (H.S.side (i+1) p)→ℂ}{Q:ι→ Coefficient F (H.S.side i p)}
  {v : ι→ F.Coeff}{u a z:ι→ℝ}
lemma Lucent.all_in (h: H.Selected)(hm:i≤N)(he : ∀ j, Lucent B H N p i Y (f j) (Q j) (v j) (u j) (a j))(hf:Dominated f)(hk:∀j, Measurable (f j))
    (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a): Lucent B H N p i Y (fun V=>∑' i,f i V) (Extra.Histories.merge (code ι) Q) (∑' i,v i) (∑' i,u i) (∑' i,a i):=by
   have hQ:=(Gig.all_in B H N p i Y h hm (fun i=>(he i).original) hf hk hv hu ha)
   refine ⟨hQ.format,hQ.agrees,hQ.leadP,hQ.future,?_⟩; choose r hl hh using fun i=>(he i).pale
   let t:=turnCost (Rout).p.order (Rout).p.power; have ht:1 ≤ t:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   have hη : Summable r:= ha.of_nonneg_of_le (fun i=>(hl i).price) (fun i=>(le_mul_of_one_le_left (hl i|>.price) ht).trans (hh i))
   refine ⟨_,Blown.joins (code ι) hl hη,?_⟩; rw [← tsum_mul_left]; exact (hη.mul_left t).tsum_le_tsum hh ha
lemma gems {X:Wing→Prop} (q:GaugeDoor Old Rout)(hq: SoundDoor (H.levels.clock.op i p) q)
    (h:H.Selected)(hm:i≤N){g:ι→ g₀}{w':ι→ Res G StartSite}{t:ι→ℂ}{φ:g₀}{ψ:Res G StartSite}{σ:ℂ}(hp:∀ j,CreamBid B H N p i Y (g j) (w' j) (t j) q X (f j) (v j) (u j) (a j) (z j))(hg:∀ U,HasSum (fun i=>g i U) (φ U))(hx:∀ i U,HasSum (fun j=> w' j i U) (ψ i U))(ht:HasSum t σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    CreamBid B H N p i Y φ ψ σ q X (fun V=> ∑' i,f i V) (∑' i,v i) (∑' i,u i) (∑' i,a i) (∑' i,z i):=by
   choose Q hQ Hq using hp
   let P:= Extra.Histories.merge (code _) Q
   have hκ:0<κ:= Real.sqrt_pos.2 (forcedPos ..)
   refine ⟨P,Lucent.all_in B H N p i Y h hm hQ hf hk hv hu ha, Tale.upon hq Hq hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=> (hQ i).bound) ha i U) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hQ i).bound),ha,le_rfl⟩⟩
   obtain ⟨ι,h,P,p,ψ,H⟩:= Hq i; exact sumBudget_credit H.purchase
end
end YM.MergeProof
