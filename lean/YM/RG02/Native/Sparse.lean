import YM.RG02.Native.Jets

/-!
# Primitive coherence from masks on neighborhoods

Problems where bandwidth fixed post-L (prep links, photon kernel rule)
need only support; automatic budgets at every finite width exponent.
We still preserve prices via issuing from SPECIFIED size. Pressure
entirely to reader, no freedom to infer uniform-in-L prices from this.
For path curvature sums bandwidth varies; must explicitly bound these
costs via constructive stencil receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Filter Finset Lattice RG Precision Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology ContDiff
variable {α β A Z: Type}
variable [NormedAddCommGroup Z] [Fintype A] [Fintype α]{n m:Side}

def inside (d:ℕ)(x:Site n) (f:A→Leaf α n) := ∀ i,separation (f i).1 x≤d
instance spanPrec (d:ℕ)(x:Site n)(f:A→Leaf α n): Decidable (inside d x f):= by unfold inside; infer_instance

def short (t d:ℕ)(U:PeriodicTable α β A Z):=∀ (n:Side)(_ : t≤n.val)(x: Leaf β n)(v:A→Leaf α n), ¬inside d x.1 v → U n x v=0
omit [Fintype α] in
private lemma bounded {d:ℕ}{x:Site n}{v:A→Leaf α n}(h:inside d x v) : length (stall x v) ≤ Fintype.card A * d:= by
   rw [exact_stall]; refine le_trans (sum_le_sum (f:=fun i=>separation (v i).1 x) (s:=univ) (fun i _=>h i)) ?_; simp

-- compare to canonical stalls at purchased n. No copies permuted. -/
variable {U: PeriodicTable α β A Z}{t d:ℕ}
private lemma stall_zero (hc:coherent t U)(hh:short t d U)(hk:t≤ n.val)(hq : 2*(Fintype.card A*d)<n.val)(h:divides n m) (r:β)(w:A→Arm α) (hp : length w≤ Fintype.card A*d) : stalls (U m) r w =stalls (U n) r w:=by
    have hx : 2*length w<n.val:= lt_of_le_of_lt (by omega) hq
    have he : stall (0:Site m) (emit 0 w)=w:= unchanged _ _ (hx.trans_le (Nat.le_of_dvd m.pos h))
    have hz : stall (0:Site n) (emit 0 w)=w:= unchanged _ _ hx
    unfold stalls; rw [if_pos he, if_pos hz]
    symm; rw [show U n (0,r) (emit 0 w)=U n (collapse h 0 (0,r)) (emit 0 w) by simp [collapse, lieBy],hc _ _ h 0 (0,r) _ hk,sum_eq_single (emit (0:Site m) w),if_pos ?_]
    · rw [collapse_emit]; simp [lieBy]
    · intro j _ hj; split
      next H=>
        apply hh _ (hk.trans (Nat.le_of_dvd m.pos h)); intro hp'; apply hj
        have hc : emit (0:Site n) (stall (0:Site m) j) =emit 0 w:=by
            rw [show (0:Site n)=lieBy h 0 0 by simp [lieBy],← collapse_emit,emit_stall,H]; simp [lieBy]
        rw [← emit_stall (0:Site m) j, ← unchanged (0:Site n) (stall (0:Site m) j) (lt_of_le_of_lt (Nat.mul_le_mul_left _ (bounded (x:=(0:Site m)) hp')) hq), hc,hz]
      rfl
    simp

omit [Fintype α] in
private lemma stall_high (hh:short t d U)(hk:t ≤ m.val)(r:β){w:A→Arm α}(hc: Fintype.card A*d< length w) : stalls (U m) r w=0:=by
    unfold stalls; split; next h=> apply hh m hk; intro hi; exact not_lt.mpr (h ▸ (bounded (x:=0) hi)) hc
    rfl

lemma same_on (hc:coherent t U)(hh:short t d U)(hk:t≤ n.val)(hq:2*(Fintype.card A*d)<n.val)(m:Side)(hm:t≤m.val): imprint (stalls (U n)) m=U m:=by
    let p : Side:= n*m
    have hu : divides n p := dvd_mul_right ..
    have hp : divides m p := dvd_mul_left ..
    have hf : stalls (U n)= stalls (U p):= by
       funext i w; by_cases h:length w≤Fintype.card A*d; exact (stall_zero hc hh hk hq hu i w h).symm
       rw [stall_high hh hk i (lt_of_not_ge h),stall_high hh (hk.trans (Nat.le_of_dvd p.pos hu)) i (lt_of_not_ge h)]
    rw [hf]; exact imprint_stalls U hc hp hm
variable [CompleteSpace Z]
lemma short.forever {w:ℝ}(h:short t d U)(hc:coherent t U)(hk:t≤n.val)(hq:2*(Fintype.card A*d)<n.val)(hw:0≤w) {C:ℝ}(he:∀ i: Leaf β n,ticket (U n) w i ≤ C) : charged t w C U:=by
    intro m hm i
    rw [← same_on (n:=n) hc h hk hq m hm]; exact (narrow_stalls _ w C he).issues hw t _ hm _
end YM.RG02.Native

namespace YM.RG02.Native
open Function Filter Finset Lattice RG Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology ContDiff
variable {α β Z:Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z][Fintype α]
variable {n:Side}

def separate (o:Site n)(d:ℕ) (x y:Ground α n):=∀ a:Leaf α n,separation a.1 o≤d→x a=y a
private def mask (o:Site n) (d:ℕ) : Ground α n →L[ℝ] Ground α n:= ContinuousLinearMap.pi fun i:Leaf α n=> if separation i.1 o ≤ d then ContinuousLinearMap.proj (φ:=fun _=>ℝ) i else 0

def localFields (t d:ℕ)(U:Stencil α β Z):=∀ n:Side,t≤n.val→∀ i:Leaf β n, ∀ᶠ x in 𝓝 (0:Ground α n × Ground α n), separate i.1 d x.1 x.2→ U n i x.1=U n i x.2
lemma follows_short {t r d:ℕ}{U:Stencil α β Z}(h:localFields t d U)(hf:fair t r U){k:ℕ}(hh:k≤r): short t d (shaped U k):=by
    intro n he i v hi
    let p:= mask i.1 d (α:=α); let f:=U n i
    have hx x : separate i.1 d x (p x):= fun a ha=> Eq.symm (by change (ite _ _ _ : Ground α n →L[ℝ] ℝ) x=_; rw [if_pos ha]; rfl)
    have hg : f =ᶠ[𝓝 0] f ∘ p := by
       have hl : Tendsto (fun i=> (i,p i)) (𝓝 0) (𝓝 0) := by change Tendsto _ _ (𝓝 ((0:Ground α n),0)); simpa using tendsto_id.prodMk_nhds (p.continuous.tendsto 0)
       filter_upwards [hl.eventually (h n he i)] with z hz; apply hz (hx z)
    unfold inside at hi; push Not at hi; obtain ⟨a,ha⟩ := hi
    have hw : p (pulse (v a))=0:= by
       ext1 j; change (if _ then _ else _ : Ground α n →L[ℝ] ℝ) _=0; split
       next H=> change pulse (v a) j=0; apply Pi.single_eq_of_ne; intro h'; rw [h'] at H; exact (not_lt.mpr H) ha
       rfl
    unfold shaped shape; rw [(hg.iteratedFDeriv ℝ k).self_of_nhds, Next.Foundations.jets_linear p ((hf n he i).of_le (Nat.cast_le.mpr hh)),ContinuousMultilinearMap.compContinuousLinearMap_apply]; exact ContinuousMultilinearMap.map_coord_zero _ a hw

-- automatically competes with regional uniform payouts. Explicit source
-- estimate needed separately for long paths. -/
variable [CompleteSpace Z] [Fintype β]
lemma auto_paid {t r d:ℕ}{a:ℝ}(U:Stencil α β Z) (ha:0≤a)(hf:fair t r U)(hg:through t r U)(hh:localFields t d U): ∃ w:ℕ→ℝ,(∀ i,0≤w i)∧ funded t r a U w:=by
    let n:Side :=⟨t+2*(r*d)+1,by omega⟩; have hn:t≤n.val:=by dsimp [n]; omega
    let w k:= ∑ i:Leaf β n,ticket (shaped U k n) a i
    have he k i:0 ≤ ticket (shaped U k n) a i:= sum_nonneg (fun i h=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    refine ⟨w,fun k=>sum_nonneg fun i _=>he _ i,fun k hk=>?_⟩
    apply (follows_short hh hf hk).forever (hg k hk) hn _ ha (fun i=> single_le_sum (fun j _=> he k j) (mem_univ i))
    rw [Fintype.card_fin]; change 2*(k*d)<t+2*(r*d)+1; have := Nat.mul_le_mul_right d hk; omega
end YM.RG02.Native
