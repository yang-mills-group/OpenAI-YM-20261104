import YM.Lodestar.TwinCost
import YM.MergeProof.South.Admit
/-!
# Exact all-sector residual representation from cutting only the
regular singleton data of a `Served` polynomial. Includes the
unchanged vacuum and all marked forced contributions. `duplicate` is
injected on EVERY original mode. Cost at the original supports and barcode
indexes (measurable masked regular sup and forced poly sup, no claim here on
higher derivative semi-norms). This is the format that Volant/Duty will actually
propagate, with the same marked denominator. We will supply the input
`Towed`s using a slight exponent loss, geometric separation and the actual
forced allowance before duplication; NOT subtract marginal evaluated
polynomials on independent gases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lodestar
open Finset Function MeasureTheory Marker Push GridApprox.Nil Lattice Wilson RG Ac MergeProof Accent Extra.Trajectories
open scoped BigOperators Classical ContDiff Topology
variable {V I Y : Type} [Fintype V] [DecidableEq V] {B:Census V} {G:Gauge} {n:Side}

section book
variable {w : V→ℝ} {M:ℕ} {e c d t:ℝ}{s:I→Support n}{o:V→Site n}
omit [Fintype V] in
lemma loci_pair {f g:Y→Poly B}(h:Loci w f c)(ht:Loci w g d): Loci w (f+g) (c+d):=by
   obtain ⟨a,hA,ha,h⟩:=h; obtain ⟨b,hB,hb,ht⟩:=ht
   refine ⟨a+b,fun i=> add_nonneg (hA i) (hB i),fun i v=> (norm_add_le _ _).trans (add_le_add (ha i v) (hb i v)),?_⟩
   unfold wordsPrice; simp_rw [Pi.add_apply,mul_add]; rw [Finset.sum_add_distrib]; exact add_le_add h ht

omit [Fintype V] in
lemma towed_pair [Fintype I]{f g:I→Y→Poly B}(h:Towed w s f M e c)(ht:Towed w s g M e d): Towed w s (f+g) M e (c+d):=by
   obtain ⟨a,ha,hA,h⟩:=h; obtain ⟨b,hb,hB,ht⟩:=ht
   refine ⟨a+b,Summable.of_finite,fun x=> ⟨fun i=>?_,Summable.of_finite,?_⟩,fun i=>loci_pair (h i) (ht i)⟩
   · dsimp only; split_ifs with he
     · rw [Pi.add_apply,add_mul]; refine add_nonneg ?_ ?_
       · simpa only [if_pos he] using ((hA x).1 i)
       simpa only [if_pos he] using ((hB x).1 i)
     rfl
   have hp1: (∑ i:I,if x ∈ s i then a i*Real.exp (e*coverNumber M (s i)) else 0) ≤ c:=by simpa only [tsum_fintype] using (hA x).2.2
   have hp2: (∑ i:I,if x ∈ s i then b i*Real.exp (e*coverNumber M (s i)) else 0) ≤ d:=by simpa only [tsum_fintype] using (hB x).2.2
   rw [tsum_fintype]; calc
    _ = (∑ i:I,if x∈s i then a i*Real.exp (e*coverNumber M (s i)) else 0)+(∑ i:I,if x∈s i then b i*Real.exp (e*coverNumber M (s i)) else 0):=by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=> by split <;> simp [*,add_mul]
    _ ≤ _:= add_le_add hp1 hp2

lemma borne_pair {i:Support n}{f g:Config G n→Poly B}(h:Borne o i f t)(ht:Borne o i g t): Borne o i (f+g) t:=by
   refine ⟨fun U D hp hP=> ?_,fun k U=> ?_,fun j=> ?_,fun U=> scope_plus (h.scope U) (ht.scope U)⟩
   · simp only [Pi.add_apply,h.home _ _ hp hP,ht.home _ _ hp hP]
   · simp only [Pi.add_apply,h.turns _ U,ht.turns _ U]
   simp_rw [Pi.add_apply,Poly.part_plus]; exact (h.me j).add (ht.me j)
lemma burns_pair {i:Support n}{f g:Config G n→ Poly B}(h:Burns o i f t)(ht:Burns o i g t): Burns o i (f+g) t:=by
   refine ⟨borne_pair h.toBorne ht.toBorne,fun U hu=>?_,fun U=> by simp only[Pi.add_apply,Poly.part_plus,h.sil, ht.sil,add_zero]⟩
   by_cases hv:f U=0
   · rw [Pi.add_apply,hv,zero_add] at hu; exact ht.permits _ hu
   exact h.permits _ hv
lemma flow_pair {i:Box n}{f g:Config G n→Poly B}(h:Flow o i f t)(ht:Flow o i g t): Flow o i (f+g) t:=by
   refine ⟨borne_pair h.toBorne ht.toBorne,fun U hu=>?_⟩
   by_cases hv:f U=0
   · rw [Pi.add_apply,hv,zero_add] at hu; exact ht.permits _ hu
   exact h.permits _ hv
omit [Fintype V] in
lemma rises_pair {f g:Poly B}(h:rises f)(ht:rises g):rises (f+g):=by
   intro i hi; rw [Poly.part_plus] at hi
   by_cases hv:f.part i=0
   · rw [hv,zero_add] at hi; exact ht _ hi
   exact h _ hv

end book

variable (R:Rep G n)(a b:V→ Config G n→ℂ)(g:V→Box n→ Config G n→ℂ)
   (H : Support n→ Config G n→Poly (Marks V))(K:Box n→ Config G n→Poly (Marks V))
   (E : Support n→ Config G n→Poly (Marks V)){o:V→Site n}{w:V→ℝ}
local notation "J!"=> Marks V
local notation "B!"=> Marks (V×Bool)
-- package all forced tails literally on unchanged support/inventory
abbrev spareK (i:Box n)(U:Config G n):Poly (Marks V):= Mach (Marks V) (fun j=>g j i U)

lemma mach_quiet (l:V→ℂ): (Mach B l).part B.quiet=0:= mute _ _
lemma mach_minus (l m:V→ℂ): Mach B (l-m)=Mach B l+Mach B (fun i=>-m i):=by
   ext i; simp only[Mach,Poly.part_plus,Poly.part_sum,Poly.part_send,Pi.sub_apply,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _=> by split <;> simp [*,sub_eq_add_neg]

lemma refit
    (U:Config G n)(he:Mach (Marks V) (fun i=>a i U-b i U)=∑ i,E i U)
    (hp:∀ i, rises (H i U)):
    duplicate V (restore R a g H K U * Poly.pass (Mach J! (fun i=>- b i U)))=
       restore R 0 0 (fun i=>duplicate V ∘ (E i+H i))
          (fun i=> duplicate V ∘ (spareK g i+K i)) U:=by
   let f := Mach J! (fun i=>a i U)+∑ i,H i U
   let q := Mach J! (fun i=>- b i U)
   have hφ:f.part (Marks V).quiet=0:=by unfold f; simp_rw[Poly.part_plus,mach_quiet,Poly.part_sum,fun i=>hop _ _ (hp i),sum_const_zero,add_zero]
   have hx : f+q=∑ i,(E i+H i) U:=by
      have hE:= mach_minus (B:=J!) (fun i=>a i U) (fun i=>b i U); unfold f q; change Mach (Marks V) (fun i=>a i U-b i U)=_ at hE -- composition?
      simp_rw [Pi.add_apply,Finset.sum_add_distrib,← he,hE]; abel
   have hv : bar R.activities B! U=fun i=> duplicate V (bar R.activities J! U i):=by
      funext i; change Poly.send (Marks (V×Bool)).quiet _= duplicate V (Poly.send (Marks V).quiet _); rw [seal_send,two_quiet]
   let l (i):= spareK g i U+K i U
   let L i:=bar R.activities J! U i+l i
   have hS : ∀ s, duplicate V (Accent.field L s)=Accent.field (fun i=> duplicate V (L i)) s:=by
      intro s; unfold Accent.field; rw [map_sum]; refine Finset.sum_congr rfl fun i _=> ?_; unfold grid; split
      · rw [map_prod]
      rw [map_zero]
   have hf: restore R a g H K U=(Real.exp (R.exponent U):ℂ) • (Poly.pass f * Accent.field L (flags R.p.threshold U)):=by
      unfold restore; unfold L l spareK f; simp_rw [add_assoc]
   rw [hf,smul_mul_assoc,mul_right_comm,← pass_add hφ (mach_quiet _),map_smul,map_mul,seal_pass _ (by rw [Poly.part_plus,hφ,mach_quiet (B:=J!) (fun i=> -b i U),add_zero]),hS]
   unfold restore; have h0:Mach B! (fun _=>0)=0:=by simp [Mach]
   simp only [Pi.zero_apply,h0,zero_add,add_zero]; rw [hx,map_sum,hv]
   simp only [Function.comp_apply,L,l,map_add,Pi.add_apply]


/-- producer at a point in the history: whole representation as needed
for downstream Duty, with costs added (we leave compression/transfer to Step
inputs). Here `b` will be a local truncation of the true coarse `a`. -/
def sheeted (P:Config G n→Poly (Marks V)) : Config G n → Poly (Marks (V×Bool)):= duplicate V ∘ couple P (-b)
lemma expense_refit (P: Config G n → Poly (Marks V)) {e c d k l:ℝ}
    (h0: P=restore R a g H K)
    (he:∀ i,Burns o i (E i) R.p.threshold)(ht: Carton o H K R.p.threshold)
    (hg:∀ i,Flow o i (spareK g i) R.p.threshold)
    (hq:∀ U, Mach (Marks V) (fun i=>a i U-b i U)=∑ i,E i U)
    (hE:Towed (fun j=>w j^2) id E R.p.B e c)(hH:Towed (fun j=>w j^2) id H R.p.B e d)
    (hG:Towed (fun j=>w j^2) Prod.fst (spareK g) R.p.B e k)(hK:Towed (fun j=>w j^2) Prod.fst K R.p.B e l)
    (hx:c+d ≤ 1)(hv:k+l≤1)(hw:∀ i,0<w i): Served R 0 0 (sheeted b P) (o ∘ Prod.fst) (w ∘ Prod.fst) e 1:=by
   let S i:= duplicate V ∘ (E i+H i); let Z i:= duplicate V ∘ (spareK g i+K i)
   have hP (i:V×Bool):0< (w ∘ Prod.fst) i:= hw _
   refine ⟨S,Z,⟨fun i=>burns_duplicate (burns_pair (he i) (ht.exp i).1),fun i=>⟨flow_duplicate (flow_pair (hg i) (ht.flag i).1), fun U=>?_⟩⟩,(towed_duplicate w (towed_pair hE hH)).shrink le_rfl hx hP, (towed_duplicate w (towed_pair hG hK)).shrink le_rfl hv hP,?_⟩
   · refine large_duplicate ?_; rw [Pi.add_apply,Poly.part_plus,hop _ _ ((ht.flag i).2 U),add_zero]; exact mach_quiet _
   funext U; rw [h0]; exact refit R a b g H K E U (hq U) (fun i=> (ht.exp i).2 U)
end YM.Lodestar
