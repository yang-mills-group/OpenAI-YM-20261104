import YM.RG3.Script.Relics

/-!
# Keep requested support K reserve through Compilation Role

When a stronger output K will still be needed at the same p, supply B+3
on rooted inputs to the slat test & stronger retention on the K model.
Still use Test, so can buy both rates at their respective stamps χ µ
but *same* inputs and coupons. This argument doesn't repeat the actual
analysis or assume stronger prices after the comp run. Doesn't get such
premises from any unadorned C.Makes; plan/payment obligations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Reserve
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Extra.Trajectories Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition Push.Local Source Estate Picnic
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V ι : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge} {w:V→ℝ}
  {P : Rep G n}

lemma series_paid {I : Type*}(f:Feed G n R ι)(g:Feed G n R I){a c v : ℝ}{B:ℕ}{m:ι→ℝ}{m':I→ℝ}
    (h:f.Worth w B a m c)(ht:g.Worth w B a m' v): (Join.series f g).Worth w B a (Sum.elim m m') (c+v):= by
  constructor
  · rintro (i|i); exact h.positive _; exact ht.positive _
  · rintro (i|i); exact h.always _; exact ht.always _
  intro x; exact Cost.sum (h.budget x) (ht.budget x)

lemma worth_lesser {f : Feed G n R ι}{B : ℕ}{a b c d : ℝ}{q:ι→ℝ}(h:f.Worth w B a q c)(hw:∀i,0<w i)(ha:b≤a)(he:c≤d): f.Worth w B b q d:= by
  refine ⟨h.positive,h.always,fun i=> budget_loosen (hit_down h.budget (fun i=> mul_nonneg (Poly.worth hw _).le (h.positive _)) ha i) he⟩

/-! support price for the post-canonical compensation. Rooted → strong Hit
uses occupancy. -/
section compile
variable {V' : Type}[DecidableEq V'][Fintype V']{S:Census V'}{ζ':V'→ Site n}
  (car : Estate n S)(T:car.Truss ι G) (F:ℕ→ Config G n→ℂ)(D:Deck S P)(q : Edition ζ' S G)
  (K:V'→ℕ) (H:Hol G)(X:(s:V')→Labels.Frame G (K s))(L:(s:V')→SectionData (X s)) {k: V'→ℝ} (hr: ∀ i, Readable H (L i) P.p n (k i)){w': V'→ℝ}

def tintfeed := Join.series (T.LogRepair F P.p).notes (Edition.tonic D (q.add (car.render ζ' F)) H L hr)
def accounts (t:ι→ℝ)(m f₁:ℕ→ℝ)(k:V'→ℝ): ℕ ⊕ V'×ℕ→ℝ:=Sum.elim ((T.LogRepair F P.p).rates t f₁) (Edition.bracken D (q.add (car.render ζ' F)) k H X m)
lemma tonic_paid {d:Deck S P}{A:Edition ζ' S G}(hz:d.contents.origins=ζ')(hc:d.Active)(hA:A.Principle P.p)(hw:∀i,0<w' i){m:ℕ→ℝ}{a d₀:ℝ}{M : ℕ}
    (hO : Occupancy ζ' M)(hl: Loaded H (a+2) m d₀ L d A k w')(ha:P.p.supportExponent ≤ a)(hd:0≤d₀):
    (Edition.tonic d A H L hr).Worth w' P.p.B (a+1) (bracken d A k H X m) ((M:ℝ)*siteFactor P.p.B*d₀):=by
  have hx i:= (trunk hr hz hc hA hl hw (by linarith) i).1
  let f:=Edition.bracken d A k H X m; have hf i:0≤f i:=(hx i.1).positive _
  let P':= Edition.tonic d A H L hr
  have hi i : P'.mode i = S.fire i.1:=rfl
  have he i : ζ' i.1∈P'.locus i:=by
    rcases i with ⟨i,j⟩; apply mem_union_right _
    simpa only [SectionData.footprint,map_zero,zero_add,scribe] using mem_image_of_mem (fun x=> wrap n x + ζ' i) (hr i).sound.anchored
  refine ⟨hf,fun i=> (hx i.1).always i.2,root_hit (mode:=fun i=>(P'.mode i).val) hO
    (fun i=> mul_nonneg (Poly.worth hw _).le (hf _)) hd (fun i _=> ⟨i.1,(show i.1∈(S.fire i.1).val from Finset.mem_singleton_self _),he i⟩) (fun x=>?_ )⟩
  let g : ℕ→ℝ:= fun i=> w' x * paidR H (a+2) m L d A k x i
  let V (i:V'×ℕ):= if x∈(P'.mode i).val then Real.exp (((a+1)+1)*coverNumber P.p.B (P'.locus i))*(Poly.toll w' (P'.mode i)*f i) else 0
  have hX:g=V ∘ Prod.mk x:=by
    funext i; change g i=(if x∈(S.fire x).val then _*(Poly.toll w' (S.fire x)*f _) else _)
    rw [if_pos (show x∈(S.fire x).val from Finset.mem_singleton_self x),Poly.solo_toll]; unfold g paidR expense
    have hs:a+1+1=a+2:=by ring
    rw [hs,mul_left_comm]; rfl
  have hr' : Function.support V ⊆ Set.range (Prod.mk x):= by
    rintro ⟨i,j⟩ hi; by_cases he':x=i
    · subst i; exact ⟨j,rfl⟩
    exfalso; apply hi; exact if_neg (show x∉(S.fire i).val from fun h=>he' (mem_singleton.mp h))
  convert Pad.absolute (Prod.mk x) (Prod.mk_right_injective _) (u:=g) (v:=V) (congrFun hX.symm) hr' (hl.2 _) using 1; ext1 i; unfold V; split_ifs <;> rfl

-- Extra grant: needs both sectors stronger than stamp p. Uses SAME coupon
-- t and output profiles cN computed at headers, since stronger emission
-- would give wrong Test.credit if not supported by original dictionaries.
lemma burthen {m f₁:ℕ→ℝ}{t:ι→ℝ}{a d₀ c₀ c₁ :ℝ}{M:ℕ}
    (hz:D.contents.origins=ζ')(h:D.Active) (he:q.Principle P.p)(hw:∀i,0<w' i)
    (hO:Occupancy ζ' M)(hE:car.Legal ζ')(_hLaw:T.Laws ζ')
    (hF: T.Strap w' P.p (a+2) c₁ t)(hs:0≤c₀)(hc:0≤c₁)
    (hi:∀ i,P.p.Regular (car.region i) (F i) ∧ ∀ x∈car.region i,P.p.supBounds x (car.region i) (F i) (f₁ i))
    (hv:∀v,SumBudget (per P.p.B (a+2) w' car.style car.region f₁ v) c₀)
    (hl:Loaded H (a+2) m d₀ L D (q.add (car.render ζ' F)) k w')(hd:P.p.supportExponent ≤ a)(hd':0≤d₀):
    (tintfeed car T F D q K H X L hr).Worth w' P.p.B (a+1) (accounts car T F D q K H X t m f₁ k) (Estimate M P c₀ c₁ d₀):= by
  apply series_paid
  · have hpost i : car.post i ∈ car.region i:=(Next.Rank.Spindle.doors _).mpr (by simp)
    apply (T.LogRepair F P.p).purchase hw (show 0≤a+1 by linarith [P.p.exponent_pos])
      (T.admission hE hw hO hc ?_) (Estate.pay hE hw hO hs (fun i=> (hi i).2 _ (hpost i)) ?_)
    · have h:a+2=a+1+1:=by ring
      exact h ▸ hF
    · have h:a+2=a+1+1:=by ring
      exact h ▸ hv
  apply tonic_paid K H X L hr hz h (principle_plus he (Estate.advised (fun i=>(hi i).1) hE)) hw hO hl hd hd'
end compile
end YM.RG3.Script.Reserve
