import YM.OPE.Pulse.Projection
import YM.OPE.Grouping.Replicate
/-!
# Resize every fiber, but without changing persisting singleton representations
Adapted from Grouping/Replicate and Birth. Rather than re-cutting marks at
all lanes at once, hold untouched some lanes. This includes genealogical
labels who still have far-away `march` budgets to recover by repeated peg,
and the signed trajectory after an inside match.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}{R:Rep G n}
  {u : (V × I)→ℂ}{a:V→Equiv.Perm V}{x:V→Site n}{m:V→Motion}{U V' : Type}

variable {g:(V×I) → Config G n→ℂ} {k:(V×I)→ℕ → Config G n→ℂ} {μ:(V×I)→Site n} {v:V} {P:Config G n→ Poly (Names V I)} {η T Z w c q b d α z : ℝ}
variable (L:Fibers I J) (s l H:ℕ) (F:J →Prop) {W:V×I→ℝ} {C:V×J→ℝ}
set_option quotPrecheck false
local notation "τ" => R.p.threshold
local notation "e₀" => R.p.supportExponent
local notation "y!"=> Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b
local notation "W₁"=>Fibers.Salt.tow W (R.p.supportExponent+c) (η/H) l
local notation "Y" => partialGroup V L
local notation "o" => μ ∘ (partialGroup V L).twig
local notation "P'" => (fun U => Fibers.reap (partialGroup V L) (P U))
local notation "n'" => (univ.filter (fun i:V×J=>F i.2))
private lemma branch_img (i:V)(l:I): (i,l)∈ (n').image (partialGroup V L).twig ↔ ∃ j,F j ∧ L.twig j=l:=by
    rw [mem_image]; constructor
    · rintro ⟨⟨j,k⟩,he,hz⟩; exact ⟨k,(mem_filter.mp he).2,congr_arg Prod.snd hz⟩
    rintro ⟨j,hj,he⟩; exact ⟨(i,j),mem_filter.mpr ⟨mem_univ _,hj⟩,Prod.ext rfl he⟩
-- `relates` remains for all symmetric copies.
variable (A:Arsenal R)
    (hC: May v m x a g (fun i=> profile R.activities (k i)) u)
    (hc:∀ i,i≠v→∀ j:I, μ (i,j)=affine (m i).1 (x i) (μ (v,j)))
    (hr:R.activities.Valid R.p z d)
    (hA:Arc R g k P v m x a μ W (R.p.supportExponent+c) (R.p.supportExponent+q) α b w u)
    (hk:∀ i,Dominated (k i))(hx:∀ i U,(P U).part ((Names V I).fire i)=coin R (g i) (k i) U)
    (hf:∀ j,F j→ L.Only j)
    (hw:∀ i,0<W i)(hγ:∀ i,0<C i)(hF:∀ i:V×J,F i.2 → C i≤ W ((partialGroup V L).twig i)) (hv:Occupancy μ s)(ht:0≤T)(hy:∀ i,W i*‖u i‖ ≤ T)(hX:0<η)(hY:η≤1)(hE:0≤ c)(hq:c≤ q)(hz₀:0≤w)
    (hH:0<H)(hσ:∀ i:V×J,((partialGroup V L).contents i).card ≤ H)(hS:∀ i:V×I,coverNumber R.p.B ({μ ((partialGroup V L).twig ((partialGroup V L).bunch i)),μ i}:Support n) ≤ l)
    (hit:∀ U,R.eval U≠0)(hu:∀ i,C i=∏ j∈(partialGroup V L).contents i,Fibers.Salt.tow W (R.p.supportExponent+c) (η/H) l j)
    (hJ: ((R.p.B + R.p.B + 1 : ℕ):ℝ)^4*(Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b) ≤ c)
    (hξ: Real.exp (Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b)-1≤ Z) {r : ℝ} (hZ:r≤ R.p.supportExponent)
local notation "t!"=> (partialGroup V L).recovered (univ.filter fun i:V×J=>F i.2) u
include A hC hc hr hA hk hx hf hw hγ hF hv ht hy hX hY hE hq hz₀ hH hσ hS hit hu hJ hξ hZ
set_option maxHeartbeats 600000 in
lemma repriced : ∃ (g':V×J→ Config G n→ℂ) (k':V×J→ℕ → Config G n→ℂ),
     (∀ i:V×J,F i.2 → g' i=g ((Y).twig i) ∧ k' i=k ((Y).twig i)) ∧
     (∀ i:V×J,¬ F i.2 → Blade R (o i) (g' i) (profile R.activities (k' i)) 0 (4*(Z/C i))) ∧ (∀ i,Dominated (k' i)) ∧ (∀ i U,(P' U).part ((Names V J).fire i)=coin R (g' i) (k' i) U) ∧
     May v m x a g' (fun i=> profile R.activities (k' i)) (t!) ∧ Arc R g' k' (P') v m x a (o) C r (R.p.supportExponent) Z Z w (t!):=by
    obtain ⟨H',K,ψ,hG,hX',hF',hK,hF'',hK',hp,hZ',hr',hd⟩:= hA.see
    let S: Fibers.Salt (V×J) (V×I) (Y) G n := ⟨μ,(Y).rebate (n') u,H',K⟩
    have hB:S.Breeze τ:=⟨hF'',hK'⟩; have hs i:W i* ‖S.pepper i‖ ≤ T:=by
       change _*‖ite _ 0 _‖ ≤ _; split_ifs; rwa [norm_zero,mul_zero]; exact hy i
    have hc'(i)(ht':i≠v) : Fibers.CopyFamily S τ (m i) (x i) (district v J) (district i J) (nome (a i)) (nome (a i)):= by
       apply familyOf S ⟨fun _=>rfl,fun _=>rfl⟩ (hp i ht').1 (fun _=> Iff.rfl) (fun _=> Iff.rfl) _ (hp i ht').2; intro j; refine ⟨hc i ht' j,?_⟩
       unfold S; simp only [Fibers.rebate, branch_img]; split; next=> exact (scalar_z _).symm
       next=> exact ((hC i ht').2 j).2.2
    let D:=S.vessel τ; let Q':=S.mount τ; let R':=S.soil τ; let Y₀:=(Y).recovered n' u
    have hO i (he:i∈n'): (Y).Only i:= by rcases i with ⟨i,j⟩; unfold Fibers.Only; rw [contentP, show L.contents j={L.twig j} from hf j (mem_filter.mp he).2, image_singleton]; rfl
    have hP(j): j∈n' ↔ F j.2:= by simp
    have hz := D.carries τ (S.wet _ hB) W₁ C R.p.supportExponent c (y!) R.p.B (S.rate W τ _ _ η s _ l hw hv hs R.p.B_pos hX hY hS H hH hσ _ _ ht hF' (hK.shrink (by linarith only [hq]) le_rfl hw) (add_nonneg R.p.exponent_pos.le hE)) R.p.exponent_pos.le (Fibers.Salt.towP _ _ _ _ hw (by positivity)) hu hJ -- placeholders?
    obtain ⟨u',ht'⟩:= S.materialize s l η T Z H hH A hB hr hZ' hw hv ht hs R.p.B_pos hX hY hS hE hF' (hK.shrink (by linarith only [hq]) le_rfl hw) hσ hit hu hJ hξ
    have hk' : Horn v m x a Q' R':=fun i hi=>⟨(hp i hi).1,fun U=>⟨fun j p hx=> ((hc' i hi).twines U p ((district_iff _ p).2 hx)).1 j,fun j p hx=> ((hc' i hi).twines U p ((district_iff _ p).2 hx)).2 j⟩⟩
    let g'(i:V×J):= if F i.2 then g ((Y).twig i) else S.debt τ i; let k'(i:V×J):= if F i.2 then k ((Y).twig i) else u' i
    let Z' U:= Mach (Bud (V×J)) Y₀ + ∑ i,Q' i U; have hV' : P'= play R (Names V J) R' Z' := funext fun U=> by rw [hd]; exact S.reimbursed R U (n') u rfl hB hO
    have hω i: Burns o i (Q' i) τ := D.clearBurn _ (S.wet _ hB) (S.turn _ hB) i; have hz'(i U): (R' i U).part (Names V J).quiet= _ := (S.taxed _ U hB i).trans (hZ' i U)
    have hU i: Dominated (k' i):=by unfold k'; split; exact hk _; exact (ht'.foot i).1
    refine ⟨g',k',fun i hi=> ⟨if_pos hi,if_pos hi⟩,?_,hU,?_,?_,?_⟩
    · intro i hi; unfold g' k'; rw [if_neg hi,if_neg hi]; exact (ht'.foot _).2
    · intro i U; by_cases hi: F i.2
      · change ((P U).part ((Y).plena _))= _; rw [(hO i ((hP i).mpr hi)).one]; rw [hx,show g' i=_ from if_pos hi, show k' i=_ from if_pos hi]
      have he : g' i=(fun U=> (Z' U).part ((Bud (V×J)).fire i)):=by
         funext U; unfold Z'; rw [Poly.part_plus, Accent.sing]; rw [show Y₀ i=(0:ℂ) from if_neg (mt (hP i).mp hi),zero_add]; unfold g'; rw [if_neg hi]; simp only [Fibers.Salt.debt, Ribbons.blank_mach,zero_add]; rfl
      rw [hV',he]; refine beach R _ R' Z' U k' hr (fun i=>hz' i U) ?_ i ((hU i).summable U) (fun j=>?_) -- rewrite lambda?
      · unfold Z'; rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact sum_eq_zero fun j _=> (hω j).sil _
      rw [show k' i=u' i from if_neg hi]; exact ht'.costs ..
    · intro i hi; refine ⟨(hp i hi).1,fun j=>?_⟩
      by_cases hu:F j
      · rw [show t! (i,j)=u (i,L.twig j) from if_pos ((hP _).2 hu), show t! (v,j)=u (v,L.twig j) from if_pos ((hP _).2 hu)]; simp only [g',k',if_pos hu]; exact (hC i hi).2 (L.twig j)
      simp only [g',k',if_neg hu]; have he:= ht'.travels (hc' i hi) (show (v,j)∈district v J from rfl); rw [show nome (a i) (v,j)=(i,j) from Prod.ext (hp i hi).1 rfl] at he;
      exact ⟨he.1,he.2,(if_neg (mt (hP (i,j)).mp hu)).trans ((scalar_z (m i)).symm.trans (congr_arg (scalar (m i)) (if_neg (mt (hP (v,j)).mp hu)).symm))⟩
    let φ(i:V×J): MergeProof.Response G n:= if F i.2 then ψ ((Y).twig i) else 0
    have hh:= (S.wet _ hB); refine ⟨Q',R',φ,?_ ,?_ ,hz.1.shrink hZ hξ hγ,hz.2.shrink le_rfl hξ hγ,hω, fun i=> D.cloudy _ hh (S.turn _ hB) i,hk',hz',?_,hV'⟩
    · constructor
      · intro i p; unfold φ; split; exact hG.yes ..; exact Attaches.zero ..
      · intro i; by_cases he:F i.2
        · exact fun j=> (show φ i=_ from if_pos he) ▸ hG.tracks _ j
        intro j; simp [φ,he]
      intro i; by_cases ht:F i.2
      · obtain ⟨f',hf',hs⟩:= hG.fee ((Y).twig i); rw [show φ i=ψ ((Y).twig i) from if_pos ht]; refine ⟨f',hf', (Finset.sum_le_sum (g:=fun j=>Real.exp ((R.p.supportExponent+q+1)*coverNumber R.p.B j)*(W ((Y).twig i)*f' j)) (fun j _ => ?_)).trans hs⟩
        apply mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [hE,hq] : e₀+1 ≤ e₀+ q+1) (by positivity))) (mul_le_mul_of_nonneg_right (hF i ht) (hf' _).1) (mul_nonneg (hγ _|>.le) (hf' _).1) (Real.exp_pos _).le
      refine ⟨0,?_⟩; simp [φ,ht,hz₀]
    · intro i hi j; by_cases he:F j
      · simp only [φ,if_pos he]; exact hX' i hi (L.twig j)
      simp [φ,he,upwards,funext_iff, stepUp, scalar_z]
    intro i j U; by_cases he:F j.2
    · have h:= (hP _).mpr he; rw [show φ j=_ from if_pos he, show k' j=_ from if_pos he, show (R' i U).part _ = _ from S.only_soil τ U hB (hO j h) i (if_pos (mem_image_of_mem _ h))]; exact hr' ..
    simp only [φ,k',if_neg he,hook,Pi.zero_apply,zero_mul,sum_const_zero,add_zero]; exact ht'.costs j i U
end YM.MergeProof.Ribbons.ManyCopies
