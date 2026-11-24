import YM.FVA2.SlotBook
import YM.PertExtension.BareSlot
/-!
# MS stencil realization for precisely the standard/calibrated SectionData choices

Here connect the exact stencil channel at any mesh/placement to the required
Wilson top. For the fitted-symbol estimates it will also be important to have
an identity for the polynomials BEFORE nonconstant sector projection.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.FVA2.Plate
open Filter Topology Set Function MeasureTheory
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book
open MS.Cylinder MS.Plane MS.Cylinder.Lab MS.Cylinder.Taylor MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension MvPolynomial
open MS.Theater
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
abbrev Glow (G:Gauge):= Dot G Lattice.Cover
abbrev Beast (G:Gauge) := Hue.Panel RG.Slot G
abbrev Page (G:Gauge) := MvPolynomial (Beast G) ℂ
abbrev use (G:Gauge):= Dark (hands G)
variable {G:Gauge}
private lemma cur_off (L:PlaqAxes)(x:Lattice.Cover)(i:G.ColorIndex)(p:QP)(a:Branch G Axis)
   (h:∀ x,a.1≠Landau.gauge x): shine L x i (a,p)=0:= by unfold shine; rw [curl_off p L _ a h, mul_zero]
abbrev beacon (i:Beast G):MS.Local.BV.Grade G:= shine i.1.plaq i.1.offset i.2
lemma pure_b (i:Beast G): Koszul.Pure (hands G) false (mono (beacon i)):= by
    rintro (_|⟨⟨z,p⟩,_|_⟩) h <;> try rfl
    apply cur_off; intro x zH; apply h; cases z; cases zH; rfl
def leadS (i:Beast G): ↥(use G):= ⟨mono (beacon i), pure_b i⟩
def buzz (G:Gauge):Page G→ₐ[ℂ] (use G) := MvPolynomial.aeval leadS
def enact (G:Gauge)(P:Page G)(U:Rig G Lattice.Cover):= (Hue.display (fun x:RG.Slot=>x.eval U) P).re
lemma enact_L (i:Beast G) : enact G (X i)=travels i.1.plaq (0:Lattice.Cover) i.1.walk i.2 := by
    funext U; rw [enact,Hue.display,MvPolynomial.aeval_X,travels,tip_at, α_at]; rfl
lemma enact_add (P Q:Page G): enact G (P+Q)=enact G P + enact G Q := funext fun U=> by rw [enact,map_add]; rfl
lemma enact_mul (P Q:Page G)(hP:Hue.Clear P): enact G (P*Q)= enact G P * enact G Q:= by
   funext U; rw [enact,map_mul]; let B := Hue.display (fun x:RG.Slot=>x.eval U); have hv: (B P).im=0:= Complex.conj_eq_iff_im.mp (hP _)
   change (B P*B Q).re=_; rw [ Complex.mul_re,hv,zero_mul,sub_zero ]; rfl

open Source (put Brand)
-- mask and min rank. For adding higher-slot terms, retain the exact function
-- (`Slot.Eval`, not only its leading log Taylor polynomial).
structure Bank (p:Glow G)(f:Source.Weights G)(r:ℕ)(L:Page G) : Prop where
   tuned : Tuned p 0
   localRep (n:Side)(x:Site n): Reads (Lab.Shift x (shown n p)) (put f x)
   below : From p.val r
   maskEq : Book.mask r (Tone.run p)=(buzz G L).val
namespace Bank
variable {p q : Glow G}{f g:Source.Weights G}{L Q:Page G}{r s:ℕ}
lemma add (h:Bank p f r L)(he:Bank q g r Q): Bank (p+q) (f+g) r (L+Q) where
   tuned:=h.tuned.add he.tuned
   below:=h.below.add he.below
   maskEq:=by simp only [map_add,Submodule.coe_add,h.maskEq,he.maskEq]
   localRep n x:=by
       obtain h:=h.localRep n x; obtain h':=he.localRep n x; rw [map_add,map_add]; refine ⟨ContDiffAt.add h.born h'.born,?_⟩; rw [Submodule.coe_add,h.home,h'.home]; exact (ink_add _ h.born h'.born).symm
lemma mul (h:Bank p f r L)(he:Bank q g s Q): Bank (couple DotFlip p q) (f*g) (r+s) (L*Q) where
   tuned:= h.tuned.pair he.tuned
   below:= by rw [Nat.cast_add]; exact h.below.pair he.below
   maskEq:= by rw [wave_cost,Nat.cast_add]; obtain hh:= pairLevel (p:=DotFlip) 0 (Fits.From_run h.below) (Fits.From_run he.below); simp only [Finset.Nat.antidiagonal_zero,Finset.sum_singleton,rankLevel,Nat.cast_zero,zero_add] at hh; rw [←hh,h.maskEq,he.maskEq,map_mul]; rfl
   localRep n x:= by rw [shown,transport_comes,shift_couple]; exact (h.localRep n x).pair (he.localRep n x)
lemma zero : Bank (G:=G) 0 0 r 0 := by
   refine ⟨Tune.zero, fun n x=>?_,fun _ _=>rfl,?_⟩
   · rw [map_zero,map_zero]; exact ⟨contDiffAt_const,(Taylor.ink_zero _).symm⟩
   rw [map_zero,map_zero,map_zero]; rfl
lemma const (t:ℝ): Bank (piece t:Glow G) (enact G (C t)) 0 (C t):= by
    refine ⟨⟨coin_symm _,fun w h=>?_, fun i=>?_⟩,fun n x=>?_,fun l he=>by omega,?_⟩
    · cases w; contradiction; rfl
    · rcases i with _ | e <;> simp [piece,coin]
    · have ht : put (enact G (C t)) x ∘ nation = fun _=> t:= funext fun a=> (by unfold enact put; simp [Hue.display]); rw [Lab.Shift,shown,transport,transport,coin_settled,coin_settled]; exact ⟨ht.symm ▸ contDiffAt_const, by rw [ht]; exact (ink_const direction _).symm⟩
    rw [buzz,MvPolynomial.aeval_C,Theater.cash1, run,coin_turn]; funext l; cases l; exact enough _ rfl; apply strange; simp; omega
lemma lesser (h:Bank p f s L)(he:r<s): Bank p f r 0 := by
    refine ⟨ h.tuned,h.localRep,fun l hv=>h.below l (by omega),?_⟩; rw [map_zero]; ext1 l; by_cases hv:(l.length:ℤ)=r; rw [enough l hv]; exact Fits.From_run h.below l (by omega); exact strange l hv
lemma lit (i:Beast G): Bank (traj (G:=G) i.1.plaq (0:Lattice.Cover) i.1.walk i.2) (enact G (X i)) 1 (X i):= by
   rw [enact_L]; refine ⟨ traj_tune ..,fun n x=>?_,by simpa using! traj_below i.1.plaq (0:Lattice.Cover) i.1.walk i.2,?_⟩; · rw [traj_copy,travels_copy]; exact travels_run ..
   rw [Nat.cast_one, mask_traj,buzz,aeval_X]; rfl
end Bank

open scoped BigOperators
local notation "deg"=> YM.PertExtension.Heat.Top.degree
variable (T:Type) (φ:T→Beast G) (l:ℕ)
lemma token (q: ℝ)(d : T→₀ℕ) : ∃ x, Bank x (enact G (rename φ (monomial d q))) (deg d) (rename φ (monomial d q)):=by
   induction d using Finsupp.induction with
   | zero=> rw [show deg (0:T→₀ℕ)=0 from map_zero (Finsupp.weight _), ← show C (R:=ℂ) (σ:=T) (↑q:ℂ)=monomial (0:T→₀ℕ) (q:ℂ) from rfl,rename_C]; exact ⟨ _,Bank.const _ ⟩
   | @single_add i e m _ _ ih =>
      clear * - T φ q i e m ih
      induction e with
      | zero=>simpa using ih
      | succ n ihn=>
       let D:= Finsupp.single i n + m
       have he : Finsupp.single i (n+1)+m= Finsupp.single i 1+D := by dsimp [D]; rw [Finsupp.single_add]; abel
       obtain ⟨u,hu⟩:=ihn; rw [he,show monomial _ (q:ℂ)=X i * monomial D (q:ℂ) from ?h]
       case h=>rw [X,monomial_mul]; simp
       rw [map_mul,rename_X, enact_mul _ _ (by intro x; simp [Hue.display]), show deg _=1+deg D by unfold Heat.Top.degree; rw [map_add,Finsupp.weight_single]; simp]; exact ⟨ _,(Bank.lit (φ i)).mul hu ⟩
lemma tokens (p:MvPolynomial T ℂ) (hv:∀ i∈p.support,l≤ deg i)(he:∀ i∈p.support,star (coeff i p)=coeff i p) : ∃ x,Bank x (enact G (rename φ p)) l (rename φ (Heat.Top.cut l p)):= by
   let Path (Q:MvPolynomial T ℂ): Prop:=∃ x,Bank x (enact G (rename φ Q)) l (rename φ (Heat.Top.cut l Q))
   have hs (s:Finset (T→₀ℕ))(h:s⊆p.support): Path (∑ i∈s,monomial i (coeff i p)):= by
       induction s using Finset.induction_on with
       | empty=> unfold Path; simp only [Finset.sum_empty,map_zero]; rw [show enact G 0=0 from funext fun i=> by rw [enact,map_zero]; rfl]; exact ⟨_,Bank.zero⟩
       | insert i s hi ih=>
           obtain ⟨x,hx⟩:= ih (Finset.Subset.trans (Finset.subset_insert ..) h); let q:= coeff i p; have he': (↑q.re:ℂ)=coeff i p:=Complex.conj_eq_iff_re.mp (he _ (h (by simp))); obtain ⟨y,hy⟩:= token T φ q.re i; rw [he'] at hy; specialize hv i (h (by simp));
           have hy:Bank y (enact G (rename φ (monomial i q))) l (rename φ (Heat.Top.cut l (monomial i q))):= by rw [Heat.Top.cut_mono]; split_ifs with hh; exact hh ▸ hy; rw [map_zero]; exact hy.lesser (lt_of_le_of_ne hv (Ne.symm hh))
           unfold Path; rw [Finset.sum_insert hi,map_add,map_add,map_add,enact_add]; exact ⟨_, hy.add hx⟩
   simpa only [← p.as_sum] using hs p.support (fun _ he=>he)

section realization
-- any sound physical top sector. Including unit without an exception.
variable {d:ℕ}{F:Labels.Frame G d}{H:YM.Source.Hol G}(S:YM.Source.SectionData F)
variable (h:S.Sound H)(p:Bid.pop S) (i:F.Index)
def bare : Source.Weights G:= fun v=> (S.evaluate (Pi.single i 1) v).re
lemma bare_put {n:Side}(o:Site n) : Source.put (bare S i) o = Orb.SlotEvaluation.fieldAt S i o:= rfl
include h
lemma prepared : ∃ y,Bank y (bare S i) (F.grades i).2 (Heat.Top.raw (Heat.Top.rendered S p).toData i)∧ Source.Brand y (bare S i):= by
   let R:= Heat.Top.rendered S p; let Q:= R.shape i; let V (k:Fin (R.count i)×G.ColorIndex):=(R.columns i k.1,k.2); obtain ⟨x,Hx⟩:= tokens (Fin (R.count i)×G.ColorIndex) (V: Fin (R.count i)×G.ColorIndex→Beast G) (F.grades i).2 Q (fun k hk=> (Heat.Top.degree_eq k).symm ▸ R.low i k hk) (by
     intro k _; have hu: coeff k (Next.Rank.Spindle.retro _ Q)=star (coeff k Q):=by unfold Next.Rank.Spindle.retro; rw [coeff_map]; rfl
     exact hu.symm.trans (congr_arg (coeff k) (Hue.Clear.actual (R.real i))))
   have ht : enact G (rename V Q) = bare S i:= by funext z;rw [bare,Heat.Top.rend_acts h p i,enact, Hue.lift_panel]; rfl
   rw [ht] at Hx; refine ⟨ x, Hx, ⟨ fun t v=>congr_arg Complex.re (h.gaugeInvariant (Pi.single i 1) t v),?_ ,Complex.continuous_re.comp (S.continuous_evaluate _), Hx.localRep ⟩ ⟩
   let W:= S.stencil×ˢ(Finset.univ (α:=Axis)); exact ⟨ W,fun u v h=> congr_arg Complex.re (S.cylinder_local _ u v (fun i hi _=> h (Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩))) ⟩
include h
lemma Bank.aura {r:ℕ}{y:Glow G}{K:Page G}(hB:Bank y (bare S i) r K) : Aura y r := by
   refine ⟨hB.below,hB.tuned,fun n=>?_⟩; let f:= Source.put (bare S i) (0:Site n); have ht:= hB.localRep n 0; refine ⟨f,when_invariant (Source.putInvariant (0:Site n) (fun g U=>congr_arg Complex.re (h.gaugeInvariant (Pi.single i 1) g U))),ht.born,?_⟩ -- variable usage h needs binder included
   rw [shift_nil] at ht; exact ht.home
end realization
end YM.FVA2.Plate
