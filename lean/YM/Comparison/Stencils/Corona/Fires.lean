import YM.Comparison.Stencils.Corona.Electron
/-!
# Equality after (un)Wick is equality of symbols, not their path spelling

No pointwise product relation is thrown away; use milking on the actual
finite curl covariance and convergence. Full-support evaluation may be
compared even with multiple representations. `Primary` here in curl ink,
use `inscribe` or define Storm for having links too. Hue and path motion
track polynomial, not presentation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Corona
open Function Filter Finset MvPolynomial Lattice
open Next Next.Rank Next.Rank.Normal
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Projection
open scoped BigOperators Topology ContDiff Classical
variable {R:Type*} {G:Gauge} {n:Side}
variable {V:Type*}

abbrev Primary (G:Gauge):= poly (Crumb G)

abbrev lanes (A:Links ℤ G.Color) (p:Crumb G):ℂ := ↑(act (Tally p.1) A p.2 : ℝ)
def demonstrates (A:Links ℤ G.Color) : Primary G →ₐ[ℂ] ℂ := aeval (R:=ℂ) (lanes A)
def Accounts (P Q : Primary G):= ∀ A : Links ℤ G.Color, demonstrates A P=demonstrates A Q

def icing : Module.End ℂ (Primary G):= milk (ambient G)
def thawed : Module.End ℂ (Primary G):= milk (-ambient G)
lemma icing_thaw (P:Primary G) : icing (thawed P)=P:=by unfold thawed icing; rw [warms,Symmetric.cancels,froze]
lemma thawed_ice (P:Primary G) : thawed (icing P)=P:=by unfold thawed icing; rw [warms,show -ambient G+ambient G=0 from Symmetric.ext (neg_add_cancel _),froze]

-- cylinder testing

def stack (B : Links (Per n) R): Links ℤ R:=fun x=>B (wrap n x.1,x.2)
lemma trace_mount (A : Links (Per n) G.Color)(p:Primary G):
   demonstrates (stack A) p= aeval (fun u:Panel n G=>((A u.1 u.2:ℝ):ℂ)) (exchange announce p):=by
    rw [reads_val]
    refine congr_arg (fun x=> aeval (R:=ℂ) x p) (show lanes (stack A)=_ from funext fun i=>?_)
    rw [reads,announce,tunes]; unfold stack aliasFor pul lanes
    rw [act_simple i.1.offset i.1.plaq]; rw [act_simple]
    simp only [PiLp.sub_apply, PiLp.add_apply,map_add,wrap_step, Complex.ofReal_sub,Complex.ofReal_add]

lemma trace_compared {p q:Primary G} (h: Accounts p q):
   exchange (announce (n:=n)) p=exchange announce q:=by
  apply MvPolynomial.funext_set (fun _=> Set.range (fun i:ℝ=>(i:ℂ))) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective)
  intro A hA
  choose v hv using fun i=> hA i (Set.mem_univ i)
  let B : Links (Per n) G.Color:=fun x=>WithLp.toLp _ (fun i=>v (x,i))
  specialize h (stack B)
  rw [trace_mount, trace_mount] at h
  rw [show A = fun u=>(↑(B u.1 u.2):ℂ) from funext fun i=> (hv i).symm]; exact h

lemma power_twilight (G : Gauge)(n:Side) : scope (announce (n:=n)) (- potential n G) = - full n G:=by
  ext1; funext p q
  rw [← power_shaped]; change treats _ _ _= -treats _ _ _
  simp only [treats,Finsupp.linearCombination_apply,Finsupp.sum]; simp only [Finset.sum_apply,Pi.smul_apply];
  change (∑ x∈(announce q).support,announce q x • ∑ y∈(announce p).support, announce p y • (-(potential n G).cov y x))= _
  simp only [smul_neg, Finset.sum_neg_distrib]
lemma switch {V Z:Type*} (Q:Symmetric V)(U:Symmetric Z)(H:V→Z→₀ℂ) (h : scope H U=Q) {p q: poly V}(he:exchange H p=exchange H q):
    exchange H (milk Q p)=exchange H (milk Q q):=by rw [← h,← prepared,← prepared,he]
lemma exposed (U:Links (Per n) G.Color) {p q:Primary G} (h: Accounts p q):
    demonstrates (stack U) (milk (full n G) p)=demonstrates (stack U) (milk (full n G) q) ∧
    demonstrates (stack U) (milk (-full n G) p)=demonstrates (stack U) (milk (-full n G) q):=by
   simp only [trace_mount, switch _ _ _ (power_shaped ..) (trace_compared h), switch _ _ _ (power_twilight ..) (trace_compared h), and_self] -- args injection?

-- proof with slot moments not relying on uniform rank conditions or supports
section Tending
variable {α:Type*} {b:Filter α} {Q : Symmetric V} {W:α→Symmetric V} {M:α→V→ℂ}{m:V→ℂ}
variable (hQ:∀ i j,Tendsto (fun x=>(W x).cov i j) b (𝓝 (Q.cov i j))) (hM : ∀ i,Tendsto (fun x=> M x i) b (𝓝 (m i)))
include hQ hM
lemma smiles {A : Type*} (Y:A→V)(s:Finset A):
    Tendsto (fun k=>blend (W k) (M k) (glyphs Y s)) b (𝓝 (blend Q m (glyphs Y s))):=by
   induction s using Finset.strongInduction with
   | _ s ih=>
    obtain rfl|⟨i,hi⟩ := s.eq_empty_or_nonempty
    · simp only [glyphs,prod_empty,fresh,tendsto_const_nhds]
    let D:= s.erase i; have hs : s=insert i D:=(insert_erase hi).symm
    have he : i∉D:=notMem_erase i s
    have hD : D⊂s:=erase_ssubset hi
    rw [hs]; simp_rw [spring _ _ _ D he]; apply ((hM _).mul (ih D hD)).add
    exact tendsto_finsetSum _ fun j _=> (hQ _ _).mul (ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) hD))
lemma converges (P:poly V):
    Tendsto (fun k=>blend (W k) (M k) P) b (𝓝 (blend Q m P)):=by
  induction P using MvPolynomial.induction_on' with
  | add u v ih ih'=> simp only [map_add]; exact ih.add ih'
  | monomial x c=>
    rw [show monomial x c=c • monomial x (1:ℂ) by rw [← map_smul,smul_eq_mul,mul_one]]
    obtain ⟨v,hv⟩:= Next.Rank.Common.letter x
    rw [hv]; simp only [map_smul]; exact (smiles hQ hM ..).const_smul _
end Tending
section Lift
variable {q:ℕ+}
local notation "reg"=> (atTop:Filter ℕ)
lemma growing (h:1<q.val): Tendsto (fun x:ℕ=> (side q x).val) reg atTop:=by
 apply tendsto_atTop_atTop.mpr
 intro d; have hL:= side_rate h 0
 have hd:∀ᶠ k:ℕ in reg, (side q k).val ≥ d:=by
   filter_upwards [hL.eventually_lt_const (by positivity : (0:ℝ)<1/(d+1:ℝ))] with k hk
   rw [pow_zero,div_lt_div_iff₀ (by exact_mod_cast (side q k).pos) (by positivity)] at hk
   apply Nat.le_of_succ_le
   exact_mod_cast (show (↑(d+1:ℕ):ℝ)≤(side q k).val from by push_cast; linarith)
 exact eventually_atTop.mp hd

lemma canonical_lift (x : Cover) (h:1<q.val): ∀ᶠ k:ℕ in reg, lift (wrap (side q k) x)=x:=by
  have he i: ∀ᶠ k:ℕ in reg, -((side q k).val:ℤ)<2*x i ∧ 2*x i≤(side q k).val:=by
     filter_upwards [(growing h).eventually_ge_atTop (2*(x i).natAbs+1)] with k hk; omega
  filter_upwards [eventually_all.mpr he] with k hk; exact lift_eq_iff.mpr ⟨rfl,hk⟩

def apoint (A:Links ℤ R) (n:Side):Links (Per n) R:=fun x=> A (lift x.1,x.2)
lemma exchange_meter (h:1<q.val)(A:Links ℤ G.Color) (i:Crumb G) :
   Tendsto (fun k : ℕ=> lanes (stack (apoint A (side q k))) i) reg (𝓝 (lanes A i)):=by
 let f:= i.1.plaq; let x:=i.1.offset
 refine tendsto_const_nhds.congr' ?_
 filter_upwards [canonical_lift x h,canonical_lift (x+step f.val.1) h, canonical_lift (x+step f.val.2) h] with k h₁ h₂ h₃
 unfold lanes; rw [act_simple,act_simple]; congr 1 -- try simp instead
 change (A _+_ -_ -_) _ = _
 simp only [stack,apoint,x,f,h₁,h₂,h₃] at *
lemma salt (A:Links ℤ G.Color){p q:Primary G} (h:Accounts p q): demonstrates A (icing p)=demonstrates A (icing q):=by
 let r:ℕ+:=2; let V k:= stack (apoint A (side r k))
 have hr:1<r.val:=by decide
 exact tendsto_nhds_unique (converges (fun i j=> circle_limit i j hr) (exchange_meter hr A) p) ((converges (fun i j=> circle_limit i j hr) (exchange_meter hr A) q).congr' (Eventually.of_forall fun k=> Eq.symm (exposed (apoint A (side r k)) h).1))
lemma melts (A:Links ℤ G.Color){p q:Primary G} (h:Accounts p q): demonstrates A (thawed p)=demonstrates A (thawed q):=by
 let r:ℕ+:=2; have hr:1<r.val:=by decide
 have he (i j:Crumb G):Tendsto (fun k=>(-full (side r k) G).cov i j) reg (𝓝 ((-ambient G).cov i j)):= (circle_limit i j hr).neg
 exact tendsto_nhds_unique (converges he (exchange_meter hr A) p) ((converges he (exchange_meter hr A) q).congr' (Eventually.of_forall fun k=> Eq.symm (exposed (apoint A (side r k)) h).2))
theorem icing_iff {p q:Primary G} : Accounts (icing p) (icing q) ↔ Accounts p q:=
 ⟨fun h A=>by simpa only [thawed_ice] using melts A h,fun h A=>salt A h⟩
end Lift
end YM.Comparison.Stencils.Corona
