import YM.OPE.Compatible.Assemblage.Inlets
/-!
# Close immediately after the grouping, consistent with all survival labels
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype W][DecidableEq W]{G:Gauge}{n:Side}
variable {A:History G}{N p i : ℕ} {P:Ensemble V}
    {X:I→ Stem V G (A.S.side i p)}{E:V→ Site (A.S.side i p)}
    {Y: Config G (A.S.side i p)→Words (V×I)}
    (L:Fibers I J)(H l:ℕ)
    {C:I→ℝ}{z:I→ℂ}{b:ℕ→ℕ}{t:ℝ}{d w:ℕ→ℝ}
set_option quotPrecheck false
local notation "m"=> A.rep N p i
local notation "e"=> (A.levels.budget i).supportExponent
local notation "u"=> scurry A.levels b w (d i) i
local notation "w'"=> grouped A d H l i C L
set_option quotPrecheck false
lemma exp_bar {x:ℝ} {n:ℕ}(h:0≤x)(ht:1≤(n:ℝ))(he:n*x ≤ 1/2): n*(Real.exp x-1) ≤ 1:=by
   have h': x ≤1/2:= (le_mul_of_one_le_left h ht).trans he; have hd : x < 1:=by linarith only [h']
   have hf:= Real.exp_bound_div_one_sub_of_interval h hd
   have hz: Real.exp x ≤ 1+2*x:= hf.trans ((div_le_iff₀ (by linarith only [hd])).2 (by nlinarith only [h',h])); nlinarith [Nat.cast_nonneg (α:=ℝ) n]
lemma exp_tilt {x:ℝ} (h:x≤1/2): Real.exp x-1≤1:=by
   rcases le_or_gt 0 x with h'|h'
   · simpa using exp_bar (n:=1) h' (by norm_num) (by simpa using h)
   have he:= Real.exp_le_one_iff.mpr h'.le; linarith only [he]
variable (hA:A.Selected)(hn:i≤ N)
lemma eroded
    (h:Arc m (lights X) (color X) Y P.v P.move E P.perms (tags X)
     (quota V (dropFunds (d i) C)) (e+1/2) (e+1) 1 (w i) (d i) (spices P z))
    (hs:ClusterPars A d w b i)(ht:Duty A b i (d i) t (w i))
    (hA:A.Selected)(hn:i ≤ N)(ho:Arsenal m)
    (hF:Fintype.card I ≤ H)(hH:0<H)(hv:Occupancy (tags X) (b i))(hp:∀ j, Marked m E P (X j))
    (hS:∀ j:V×I, coverNumber (A.levels.budget i).B ({tags X (j.1,L.twig (L.bunch j.2)),tags X j}:Support _)≤ l)
    (hK:∀ j U,(Y U).part ((Names V I).fire j)=coin m (lights X j) (color X j) U)
    (hC:∀ j,0<C j)(hJ:∀ j,C j*‖z j‖ ≤ 1) :
    ∃ U:J→Stem V G (A.S.side i p),
      (∀ j,(U j).home=(X (L.twig j)).home) ∧
      Owns m E P U w' (e-3) (fun v0=> (partialGroup V L).reap (Y v0)) ∧
     (∀ j,L.SingleFiber j → U j=X (L.twig j))∧∀ j,¬ L.SingleFiber j → Blade m
       ((U j).home P.v) ((U j).oil P.v) (profile (m).activities ((U j).gas P.v)) 0 (4*(1/w' j)):=by
    have hL : A.Conv N p i:= hA.represents N p i hn; have hν := hL.vac; let Z:=(m).p; have hu':0 < d i:= ht.hats.1
    let Z':= quota V (dropFunds (d i) C); have hW (j):0<Z' j:=mul_pos hu' (hC _); have hD: ∀ j,Dominated (color X j):=fun j=>(hp j.2).spends j.1
    have hr : Collar (tags X) P.v E P.move:=fun j hj x=> (hp x).sym _ hj; have hj U:(m).eval U≠0:= (Tour.bright A hA N p i hn U).ne'
    have hξ(t): (quota V (w')) t= ∏ j∈(partialGroup V L).contents t, Fibers.Salt.tow Z' (Z.supportExponent+1/2) (d i/H) l j:=by change grouped A d H l i C L t.snd = _; unfold Z; rw [hν]; exact grouped_b H l L t -- notation
    have hQ(j):0 < grouped A d H l i C L j:= grouped_pos H l L hu' hH hC _; have hb: Occupancy (tags X ∘ (partialGroup V L).twig) (b i):=by
       let f:= partialGroup V L; intro y; let S:= univ.filter (fun j=> ((tags X) ∘ f.twig) j=y); have h' : S.image f.twig⊆ univ.filter (fun j=>tags X j=y) :=by
          intro i hi; obtain ⟨x,hx,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
       change S.card≤_; exact (card_image_of_injective S f.sectioned.injective).symm.le.trans ((card_le_card h').trans (hv y))
    have hyz(j:V×I): Z' j*‖spices P z j‖≤1:=by
       rw [spices, P.price]; exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hC j.snd|>.le) ht.hats.2) (norm_nonneg _)).trans (hJ _)
    rw [← hν] at h
    obtain ⟨g',k',hx,hT,he,hM,ha,hu⟩:= perennial (Z:=1) H l L (b i) h ho hL.good.labels (linked P X hp z) hr hj hD hK hW hv (T:=1) zero_le_one hu'.le hyz hu' ht.hats.2 hH hF (hν.symm ▸ hS) (by rw [hν]; exact hs.bars.1) (by rw [hν]; exact hs.bars.2) hξ
    have hΦ:0 ≤ w i:=by
       obtain ⟨F,Z',ψ,-,-,-,⟨v0,hD,hw,H⟩,-⟩ := h.see
       exact (tsum_nonneg (hw 0|>.1)).trans (hw 0|>.2.2)
    let f':= partialGroup V L; let y:= u
    have hk : 0 ≤ y:=by unfold y scurry Salt.scent; positivity
    let b' := A.levels.budget i; let V0:= (b'.B+b'.B+1)^4
    have h4:(4:ℝ) ≤ V0:=by
      suffices hh:4≤V0 by exact_mod_cast hh
      have hb':2 ≤ b'.B+b'.B+1:=by have := b'.B_pos; omega
      exact (le_trans (by decide : 4≤(2:ℕ)^4) (Nat.pow_le_pow_left hb' 4))
    have hw' : V0*(Real.exp y-1 : ℝ) ≤ 1:= exp_bar (n:=V0) hk (by linarith only [h4]) (by unfold V0; rw [Nat.cast_pow]; exact hs.bars.1)
    let μ:= (b i)*siteFactor b'.B *d i
    have hv' : V0*μ ≤ 1/2:= by
        have hf: (V0:ℝ)*(w i+μ) ≤ 1/2:=by unfold V0; rw [Nat.cast_pow]; exact ht.stakes.1
        nlinarith only [hf,h4,hΦ]
    let τ:= Real.exp y-1+μ; have hτσ: V0*τ ≤ 2:= by unfold τ; linarith only [hw',hv']
    have ht': Real.exp τ-1 ≤ 1:= exp_tilt (by nlinarith only [h4,hτσ])
    have hξ': Real.exp y-1≤1:=hs.bars.2
    rw [hν] at hx -- Z?, affects L.rep? okay
    let Y':= fun v0=> (partialGroup V L).reap (Y v0)
    let w'₀:= grouped A d H l i C L; let p':= quota V w'₀; let o:=tags X ∘ (partialGroup V L).twig
    have hPzz: Serves m g' (fun j=>profile (m).activities (k' j)) Y' P.v P.move E P.perms o p' (e-3) 1:=by
       -- thru requires GAP between Arc's TWO e,d. current both e. shrink first.
       obtain ⟨F',K',ψ',h1,h2,h3,hf⟩:= hx.see; have hw₁ j:0<p' j:= hQ j.2
       have hP: Arc m g' k' Y' P.v P.move E P.perms o p' (e-3+0) e (Real.exp y-1) (Real.exp y-1) (d i) (f'.bypass (spices P z)):= ⟨F',K',ψ',h1,h2,h3.shrink (by linarith only) le_rfl hw₁,hf⟩
       apply thru hP hL.good.labels hw₁ hu'.le hb (by linarith only [ht.exp]) ?_ hw₁ (Z:=1) (by intro j h S _; simp) zero_le_one (by simpa using hξ') ?_ ha he hj
       · rw [hν,← Nat.cast_pow]; refine le_trans (show _ ≤ _ from hτσ) ?_; linarith only
       rw [hν]; simpa only [one_mul] using ht'
    let U(j:J):Stem V G (A.S.side i p):= ⟨(X (L.twig j)).home,fun i=>g' (i,j),fun i=> k' (i,j)⟩; refine ⟨U,fun _=>rfl,⟨?_,hQ,hPzz⟩,fun j hj=> ?_,?_⟩
    · intro j; exact ⟨fun v hi=> (hp _).sym v hi,fun i hi=> ⟨((hM i hi).2 j).1,((hM i hi).2 j).2.1⟩, fun i=>he (i,j)⟩ -- add
    · have ht : (U j).oil=(X (L.twig j)).oil:= funext fun i=>(hT (i,j) hj).1; have ht' : (U j).gas=(X (L.twig j)).gas:=funext fun i=>(hT (i,j) hj).2; exact congr_arg₂ (fun y z => Stem.mk ((X (L.twig j)).home) y z) ht ht'
    exact fun j hj=> hu (P.v,j) hj
end YM.MergeProof.Ribbons.ManyCopies
