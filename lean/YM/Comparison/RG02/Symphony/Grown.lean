import YM.Comparison.RG02.Symphony.Roster
/-! Transport Offer at every grade through kreset, applying the Offer linearity checks
from stationary Fk *after estimating* (also see Seed). Deterministic coefficient
convention; for kreset adjustment in the actual trajectory consumed by Actual etc. Need
analytic-offer/zero momentum reachability data (keep same widths throughout cycle -- not
implying suppliers here). Keep the stationary alpha sign, determinant conventions paid, and
polynomial order rank explicitly (field count ≤ k + 2 etc). -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.L2Operator
variable {G:Gauge}{N:ℕ→Side} (H:Columns G N) (r k i:ℕ) {u:ℕ→ℤ}
    (C:Caliber)(b:ℕ→SpecK G)
namespace Grown
set_option quotPrecheck false
local notation "w"=> C.back r
local notation:100 "ψ[" j "," i "]"=> motion (money (C.back r) 0 j 2) i

def inverse (H:Columns G N) (C:Caliber)(r:ℕ) : Columns G N:= fun k i=> born (fun n=>H n i) (C.back r) 0 r k
def forecast (C:Caliber)(r:ℕ)(b:ℕ→SpecK G)(k:ℕ):SpecK G := ∑ j∈range (r+1), motion (money (C.back r) 0 j 2) k • b j
local notation "U"=> inverse H C r
local notation "V"=> forecast C r b
variable (he:∀ i,Charge r u (fun j=> H j i))(hv:Monotone u)
private lemma real(j:ℕ) : Rim (ψ[j,k]):= Preserves.motion_real (monetized w 0 j 2) (Eventually.of_forall fun x=> ((Rim.ofReal x).pow j).mul (Rim.ofReal _)) k
include he hv
lemma rank : ∀ i,Charge r u (fun j=> U j i) := fun i k hp=> apportion w 0 r (he i) k hp (fun _ hi=>hv hi.le)
lemma shown (hk:k≤r) : Clarity.value ((inverse H C r) k i)=∑ j∈range (r+1),(ψ[j,k]).re • Clarity.value (H j i) := by
    apply pairing_ext; intro x y; rw [Clarity.reads ((rank H r C he hv i k hk).smooth.contDiffAt) , show iteratedFDeriv ℝ 2 (inverse H C r k i) 0= _ from Ranking.pay _ _ (he i) _ _, sum_mulVec,dotProduct_sum]; let X:=chartEquiv G (N i)
    let p:= fun j:ℕ=> iteratedFDeriv ℝ 2 (H j i) 0 ![X x,X y]
    have hv : ((∑ j∈range (r+1),ψ[j,k] • iteratedFDeriv ℝ 2 (H j i) 0) (![X x,X y]))=∑ j∈range (r+1), ψ[j,k] * p j:= by rw [_root_.sum_apply]; rfl
    rw [hv, Complex.re_sum, ← sum_neg_distrib]; apply sum_congr rfl; intro j hj; have hu:=mem_range_succ_iff.mp hj; rw [Matrix.smul_mulVec,dotProduct_smul, Clarity.reads ((he i j hu).smooth.contDiffAt), ← (real r k C j).re]; unfold p X; simp
variable (hG:G.Simple)(a:G.ColorIndex)
    (hc:∀ k≤r,Offer (b k) (H k))
include hc
lemma provides (hk:k≤r): Offer ((forecast C r b) k) (inverse H C r k):= by
    have h := Offer.alongS (range (r+1)) (fun j=> (ψ[j,k]).re) (fun i hi=> hc i (mem_range_succ_iff.mp hi)) (fun i=> shown H r k i C he hv hk)
    simp_rw [show ∀ j:ℕ,((ψ[j,k]).re:ℂ)=_ from fun j=> (real r k C j).re] at h; exact h

-- exact high convention, price off p=0 on the independent symbol. not guessing from C.path β.
variable (hs:∀ i,Sheet r (fun k=>H k i)) (hy:∀k≤r, ∀ i s,H k i ∘ shifts s 0=H k i)
include hs hy hG
omit hc
omit hv in
lemma body(hk:k≤r): ∀ i,Clarity.Body (H k i):= fun i=> Clarity.earned (hs i) (he i) hk hG (hy k hk i)
lemma after(hk:k≤r): ∀i, Clarity.Body (inverse H C r k i):= fun i=> Clarity.earned (Call.certified 0 r (he i) w (hs i)) (rank H r C he hv i) hk hG (fun s=> Adjacent.point 0 r (shifts s 0) (fun k hk=> hy k hk i s) w k)
structure Canon (C:Caliber)(H:Columns G N)(r:ℕ):Prop where
  paid k: k≤r → ∃ s:SpecK G, Offer s (H k) ∧ (∀ a:G.ColorIndex, probe₂ s a = (C.measure k:ℂ))
variable (ht:Expands N) (ha : Canon C H r)
omit he hv hc hs hy hG
include hc ha ht
lemma evidence (hk:k≤r) : probe₂ (b k) a=(C.measure k:ℂ) := by obtain ⟨s,h,hp⟩:= ha.paid _ hk; rw [(hc k hk).unique_price a ht h, hp]
omit hc in
include a in
lemma unique_coeff (hr':k≤r) {d:Caliber}(h': Canon d H r): d.measure k=C.measure k := by
  obtain ⟨s,h,hp⟩:= ha.paid _ hr'; obtain ⟨q,hq,he⟩:= h'.paid _ hr'; exact Complex.ofReal_inj.mp ((he a).symm.trans ((hq.unique_price a ht h).trans (hp a)))
-- construct canon from applicable Offers all finitely many and ψ symbol price for each (>0) (NOT assuming appropriate β matching)
omit ha ht hc in -- tidy exclude
private lemma commitment (hq:∀ k≤r,∀a:G.ColorIndex,probe₂ (b k) a=(C.measure k:ℂ))(hc: ∀k≤r,Offer (b k) (H k)) : Canon C H r := ⟨fun k hk=> ⟨_,hc k hk,hq k hk⟩⟩
omit ha ht hc in
def prescribes (b:ℕ→SpecK G)(a:G.ColorIndex): Caliber where
    measure i:= if i=0 then 1 else (probe₂ (b i) a).re
    starts:= if_pos rfl
omit ha
include he hs hy hG hc ht
lemma making (hq:probe₂ (b 0) a=1) : Canon (prescribes b a) H r:= by
    refine commitment H r (prescribes b a) b (fun k hk c=> ?_) hc; rw [(hc k hk).color_one a ht (body H r k he hG hs hy hk) c hG]
    unfold prescribes; dsimp only; split; next he=> subst k; rw [hq,Complex.ofReal_one]
    exact ((hc k hk).paid a ht (body H r k he hG hs hy hk)).symm
include ha
omit he hs hy hG in
lemma response ( _:k≤r): probe₂ (forecast C r b k) a= if k=0 then 1 else 0:= by
    have h:=Offer.payment a (range (r+1)) (fun j=> (ψ[j,k]).re) (fun i hi=> hc i (mem_range_succ_iff.mp hi)); simp_rw [show ∀ j:ℕ,((ψ[j,k]).re:ℂ)=_ from fun j=>(real r k C j).re] at h; exact h.trans ((sum_congr rfl fun j hj=> by rw [evidence H r j C b a hc ht ha (mem_range_succ_iff.mp hj)]).trans (C.horizon ..))
include hv a
lemma vanished (hk:k≤r) (hh:k≠0): Signature.Short (forecast C r b k) 4 := by
    have he':= after H r k C he hv hG hs hy hk; let hp:= (provides H r k C b he hv hc hk); have hP:= hp.signature ht he'; exact hP.short_four_of_short_three hp.smooth (hP.short_three hp.smooth hG (a:=a) (by rw [response H r k C b a hc ht ha hk, if_neg hh]))

end Grown
end YM.Comparison.RG02.Symphony
