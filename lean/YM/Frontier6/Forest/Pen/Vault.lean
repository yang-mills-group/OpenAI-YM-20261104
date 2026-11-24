import YM.Frontier6.Forest.Pen.Trimming

/-! One step in descending a finite spectrum. Project through any allowed
 horizon (all the lower budgets at root can already be killed exactly).
 Keep ancestor projection and all revenue in the same grammar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest.Face
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T: Fareway I}{K:Final C H S}{P Q:Fabric I}{A B:Art S I}{L L':Finset ℝ}{b a w r:ℝ}{x:I→ E4}
variable (hC:Road.Ribbon C H S)(top:Forest.Top K T L L' r) (h:Face K T L' r a P w A)(he:Pen K T L a P A w)(ha:a∈ L) (hp:Local T P x a)
include hC top h he ha hp
lemma accrue (d:ℕ)(hc:Forest.Centered T P x K d): T.Costs (fun i=> pitch K (x i) d (A i)) (w-d*a):=by
    rcases (top.apex _ ha).2.eq_or_lt with hh|hh
    · exact Mist.relevant K hC (hh.symm ▸ h.private_ hh) hp (top.apex _ ha).1 d hc
    obtain ⟨u,hu,hQ⟩:= h.outer hh; have hr:= top.apex _ ha|>.1.trans_lt hh; obtain ⟨k,hk,hU⟩:= (hQ.and (hu.shineout hC hr hc he.intact (hQ.mono fun i hi=> hi.intact) (w-d*a))).exists
    exact ((top.routed hr|>.head P (u k) w a hk (top.smaller a ha hh) d x hp hc).add hU).cf (Eventually.of_forall fun i=>by simp)
lemma pass (hx:Contains T Q x)(d:ℕ)(hc:Forest.Centered T P x K d): Face K T L' r b Q (w-d*(a-b)) (fun i=> part K (x i) d (A i)):=by
    let Y(i:I):= pitch K (x i) d (A i); have ht:= accrue hC top h he ha hp d hc; rw [show w-d*(a-b)= w-d*a + d*b by ring]; refine ⟨fun ha'=>?_,fun ha'=>?_⟩
    · refine ⟨fun _ i=>part K (x i) d (A i), Prism.hue d hx (v:=Y) (v':=fun _=>Y) ht ?_, Eventually.of_forall fun _=> Pen.suits K d ht hx⟩; exact fun _=> Eventually.of_forall fun _=> Fareway.Costs.free.cf (Eventually.of_forall fun _=>by simp)
    exact ha'.symm ▸ Mist.suits K d _ hx ht -- r→b equality convert check
omit top h he ha hp
lemma deepen (hw:Mist T r P A w)(hx: Local T P x r)(hc:Contains T P x)(hr:0<r)(hb:b≤r)(z:ℕ) (he:∀ (d:ℕ),d<z→∀ᶠ i in T.via,pitch K (x i) d (A i)=0): Prune K T L' r b P (w-z*(r-b)) A:=by
    refine ⟨_,Prism.full hw hx hr hc, Eventually.of_forall fun d=>?_⟩
    have hV(t:Fin (d+1)): Pen K T L' b P (fun i=> part K (x i) t (A i)) (w-z*(r-b)):=by
       rcases le_or_gt z (t:ℕ) with ht|ht
       · exact (Pen.suits K t (hw.painted K hC hx hr t) hc).mono (by linarith only [mul_le_mul_of_nonneg_right (show (z:ℝ) ≤ (t:ℝ) by exact_mod_cast ht) (sub_nonneg.mpr hb)])
       refine Pen.zero.cf ((he t ht).mono fun i hi=>?_); change 0= suit K (x i) t (pitch K (x i) t (A i)); rw [hi,map_zero]
    exact (Pen.sums Finset.univ (V:=Fin (d+1)) (fun t _=> hV t)).cf ((lights K d (hx.ready K hr d) hw.acts).mono fun i hi=>(all_from_parts K d _ _ hi).symm) -- all_from arg? fill
include top h ha hp
lemma feeds (hb:b∈L)(hz:b≤a)(hx: Contains T P x): Face K T L' r b P w A:=by
    rcases (top.apex _ ha).2.eq_or_lt with he|he
    · subst r; have hu:= h.private_ rfl; refine ⟨fun hv=>?_,fun hv=>?_⟩
      · simpa only [Nat.cast_zero,zero_mul,sub_zero] using deepen (L':=L') hC hu hp hx ((top.apex _ hb).1.trans_lt hv) hz 0 (fun i hi=> False.elim (by omega))
      exact hu
    refine ⟨fun hv=>?_,fun hv=>?_⟩; obtain ⟨v,hv,hV⟩:= h.outer he; exact ⟨v,hv,hV.mono fun i hi=>hi.feed (top.smaller _ ha he) hz hp hx⟩
    linarith
end YM.Frontier6.Forest.Face
