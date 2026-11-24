import YM.OPE.Compatible.Assemblage.Vessel
import YM.OPE.Sweep.Net

/-!
After remounting can insist on all solitary labels including forced
tallies. Pose witnesses at the given arbitrary orientation/copy, same
costs through regroup.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n:Side}{R:Rep G n}
    {u :(V×I)→ℂ}{a:V→Equiv.Perm V}{x:V→Site n}{m:V→Motion}
variable {g:(V×I)→ Config G n→ℂ} {k:(V×I)→ℕ→ Config G n→ℂ}{μ:(V×I)→Site n}{v:V}{P:Config G n→Poly (Names V I)} {η T Z χ τ φ q d b : ℝ}
    (H l :ℕ) (L:Fibers I J) {W:(V×I)→ℝ} {C:(V×J)→ℝ}(s:ℕ)
set_option quotPrecheck false
local notation "e" => R.p.supportExponent
local notation "s!"=> Ribbons.Salt.scent R.p.B s (R.p.supportExponent+1/2) T η 1 φ
local notation "Y!" => (partialGroup V L)
local notation "P'"=> fun U=> Fibers.reap (partialGroup V L) (P U)
local notation "W₁"=>Fibers.Salt.tow W (R.p.supportExponent+1/2) (η/H) l
lemma alone (v:V)(i:J) : (partialGroup V L).SingleFiber (v,i) ↔ L.SingleFiber i:=by
   unfold Fibers.SingleFiber; rw [contentP]; let q:= (fun i':I=> (v,i')); change Finset.image q _={q (L.twig i)} ↔ _
   rw [← image_singleton]; exact (Finset.image_injective (show Injective q from fun a b h=> Prod.mk_inj.mp h|>.2)).eq_iff
lemma only (i:V×J): (partialGroup V L).SingleFiber i ↔ L.SingleFiber i.2:= alone L i.1 i.2
lemma shade_ink (i:V×I): (partialGroup V L).shade u i=(if L.SingleFiber (L.bunch i.2) then 0 else u i):=by
   unfold Fibers.shade Fibers.divert Fibers.bypass; simp only [only,Pi.sub_apply,comp_apply]
   change u i-(if L.SingleFiber (L.bunch i.2) then _ else _) = _; split; next h=> rw [(show (partialGroup V L).twig (_)= i from ((partialGroup V L).sola _ ((only ..).mpr h) i|>.1 rfl).symm), sub_self]
   next=> rw [sub_zero]
variable (hA:Arc R g k P v m x a μ W (R.p.supportExponent+1/2) (R.p.supportExponent+1) 1 φ χ u)
   (A:Arsenal R)(hr:R.activities.Valid R.p d b)(hV:May v m x a g (fun i=>profile R.activities (k i)) u)(hB:Collar μ v x m)
   (hp : ∀ U,R.eval U≠0)(hm:∀ i,Dominated (k i)) (hk:∀ i U,(P U).part ((Names V I).fire i)=coin R (g i) (k i) U)
include hA A hr hV hB hp hm hk
set_option maxHeartbeats 200000 in
lemma perennial (hw:∀ i,0<W i)(hv:Occupancy μ s)(ht:0≤T)(hb:0 ≤ χ)(hg:∀ i,W i * ‖u i‖ ≤ T)(hX:0<η)(hY:η≤1)(hH:0 < H)
    (hF:Fintype.card I ≤ H)(hS:∀ i:V×I, coverNumber R.p.B ({μ ((Y!).twig ((Y!).bunch i)),μ i}:Support n)≤ l)
    (hJ: (((R.p.B+R.p.B+1:ℕ):ℝ))^4*s! ≤ 1/2)(hξ: Real.exp (s!)-1≤ Z)
    (hT:∀ i,C i=∏ j∈(Y!).contents i, W₁ j):
    let o := μ ∘ (partialGroup V L).twig
    let q := (partialGroup V L).bypass u
    ∃ g':(V×J)→ Config G n→ℂ,∃ k':(V×J)→ℕ→ Config G n→ℂ,
     Arc R g' k' (P') v m x a o C e e (Real.exp (s!)-1) (Real.exp (s!)-1) χ q ∧
     (∀ i:V×J,L.SingleFiber i.2 → g' i= g ((Y!).twig i)∧ k' i=k ((Y!).twig i))∧
     (∀ i,Dominated (k' i)) ∧ May v m x a g' (fun i=>profile R.activities (k' i)) q ∧
     (∀ i U,((Y!).reap (P U)).part ((Names V J).fire i)=coin R (g' i) (k' i) U)∧
     ∀ i:V×J,¬ L.SingleFiber i.2 → Blade R (o i) (g' i) (profile R.activities (k' i)) 0 (4*(Z/C i)) :=by
   intro o q'; let L':= Y!; let t:= R.p.threshold
   obtain ⟨F,K,ψ,hψ,hP,hG,hK,hD,hW,hY',hR,hM,hy⟩:= hA.see
   let S:Fibers.Salt (V×J) (V×I) L' G n:= ⟨μ,L'.shade u,F,K⟩
   have hB' : S.Breeze t:= ⟨hD,hW⟩
   have hy': ∀ i,W i*‖S.pepper i‖≤T:= by
      intro i; change W i*‖L'.shade u i‖≤T; rw [shade_ink]; split; next=> simpa using! ht
      next=> exact hg i
   have hE:= hK.shrink (show e+1/2 ≤ e+1 by linarith only) le_rfl hw
   have hF':=cardinal_le (V:=V) H L hF -- implicit V needs annotate
   obtain ⟨u',hz⟩:= S.materialize s l η T Z H hH A hB' hr hR hw hv ht hy' R.p.B_pos hX hY hS (by norm_num : (0:ℝ) ≤ 1/2) hG hE hF' hp hT hJ hξ
   let Q:= Fibers.Salt.income R S -- income notation
   have ha (i:V×J)(h:L.SingleFiber i.2):C i≤W (L'.twig i):=by
      have hp:η/H≤1:= (div_le_self hX.le (by exact_mod_cast hH : 1≤ (H:ℝ))).trans hY
      have he: 0 < e+1/2:= add_pos R.p.exponent_pos (by norm_num)
      rw [hT,(only ..).mpr h, Finset.prod_singleton]; change _ ≤ W ((Y!).twig i); unfold Fibers.Salt.tow; -- inspect
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      exact (mul_le_of_le_one_left (hw _|>.le) hp).trans (le_mul_of_one_le_right (hw _|>.le) (Real.one_le_exp (mul_nonneg he.le (by positivity))))
   let q := S.debt t
   let g' i:= if L.SingleFiber i.2 then g (L'.twig i) else q i
   let k' i:= if L.SingleFiber i.2 then k (L'.twig i) else u' i
   let ψ'(i:V×J) := if L.SingleFiber i.2 then ψ (L'.twig i) else 0
   have hwC i:0<C i:= by rw [hT]; exact prod_pos (fun i _=> Fibers.Salt.towP _ _ (η/H) _ hw (by positivity) _)
   have he(i:V)(hi:i≠v): Fibers.CopyFamily S t (m i) (x i) (district v J) (district i J) (nome (a i)) (nome (a i)):=by
      apply familyOf S (default_perm (a i)) ((hY' i hi).1) (fun _=> Iff.rfl) (fun _=> Iff.rfl) _ (hY' i hi).2
      intro j; refine ⟨hB i hi j,?_⟩; change L'.shade u (i,j)= scalar (m i) (L'.shade _ _); rw [shade_ink,shade_ink]; dsimp only; split; exact (scalar_z _).symm; exact ((hV i hi).2 j).2.2
   have heK(γ:V×J)(b:L.SingleFiber γ.snd):u (L'.twig γ) - L'.divert u (L'.twig γ)=0:=by
      change L'.shade u (L'.twig γ)=0; rw [shade_ink]; exact if_pos (by cases γ; change L.SingleFiber (L.bunch (L.twig _)); rwa [L.sectioned])
   have hC: Garnish R.p o ψ' C e χ:=by
      refine ⟨fun i t=> ?_,fun i t=>?_,fun i=>?_⟩
      · unfold ψ'; split; next=> exact hψ.yes ..
        next=> exact Attaches.zero _ _
      · unfold ψ'; split; next=> exact fun he=> hψ.tracks _ _ he
        next=> exact fun he=>False.elim (he rfl)
      unfold ψ'; split
      next hx =>
        obtain ⟨y,he,hU⟩:= hψ.fee (L'.twig i); refine ⟨y,he,le_trans (Finset.sum_le_sum fun j _=>?_) hU⟩
        refine (mul_le_mul ?_ (mul_le_mul_of_nonneg_right (ha i hx) (he j).1) (mul_nonneg (hwC i|>.le) (he j).1) (Real.exp_pos _).le); gcongr; linarith only
      next hx=> exact ⟨0,by simp,by simpa using hb⟩
   have hρ:relates v m x ψ':= by
     intro i hi j; unfold ψ'; change (if L.SingleFiber j then _ else _)= upwards _ _ (if L.SingleFiber j then _ else _); split; next=> exact hP i hi _
     next=> exact funext fun a=> funext fun b=> (scalar_z _).symm
   obtain ⟨heT,heP⟩:= S.parked s l H η T hB' hw hv ht hy' hX hY hH hS (by norm_num : (0:ℝ) ≤ 1/2) hG hE hF' hT hJ
   have hz': (P')= play R (Names V J) (S.soil t) (fun U=>Mach (Names V J) q'+ ∑ i,S.mount t i U):=by
      funext U; rw [hy]; exact S.transient (R:=R) u (show _=_ from by unfold Fibers.shade; abel) rfl hB' U
   refine ⟨g',k',⟨S.mount t,S.soil t,ψ',hC,hρ,heT,heP,(S.vessel t).clearBurn t (S.wet _ hB') (S.turn _ hB'),(S.vessel t).cloudy t (S.wet _ hB') (S.turn _ hB'),?_,fun i U=> (S.taxed t U hB' i).trans (hR i U),fun i j U=>?_, hz'⟩, fun i hi=>⟨if_pos hi,if_pos hi⟩, fun i=> ?_, ?_, ?_,fun i hi=> ?_⟩
   · intro i hi; refine ⟨(hY' i hi).1,fun U=> ⟨fun j p ht=> ?_,fun j p ht=>?_⟩⟩
     · exact ((he i hi).twines U p ((district_iff v p).mpr ht)).1 j
     exact ((he i hi).twines U p ((district_iff v p).mpr ht)).2 j
   · unfold ψ' k'; split
     next hj => rw [S.kept_fire _ _ hB' _ ((only ..).2 hj) (heK j hj)]; exact hM i (L'.twig j) U
     next he' => rw [show hook R.activities R.p.threshold 0 i U=0 from (by simp [hook]), add_zero]; exact hz.costs ..
   · unfold k'; split; exact hm _; exact (hz.foot _).1
   · intro i hi; refine ⟨(hY' i hi).1, fun j=>?_⟩; unfold g' k' q' Fibers.bypass; simp only [only]; change (if L.SingleFiber j then _ else _)= _ ∧ _
     split
     next hj=> exact ⟨((hV i hi).2 (L.twig j)).1, by simpa only [if_pos hj] using! ((hV i hi).2 (L.twig j)).2.1, by simpa only [if_pos hj] using! ((hV i hi).2 (L.twig j)).2.2⟩ -- right simplifies elsewhere
     next hj=> obtain ⟨hu',hx⟩:= hz.travels (he i hi) (show (v,j)∈district v J from rfl); rw [show (nome (a i) (v,j))=(i,j) from Prod.ext (hY' i hi).1 rfl] at hx hu'; exact ⟨hu',by simpa only [if_neg hj] using! hx,by simp [scalar_z]⟩
   · intro i U; by_cases hh:L.SingleFiber i.2
     · change (P U).part ((Y!).plena _)=_; rw [(Y!).solo_plena i ((only L i).mpr hh)]; unfold g' k'; rw [if_pos hh,if_pos hh]; exact hk ..
     have hw : q' i=0:= if_neg ((by exact mt (only ..).1 hh) : ¬ (Y!).SingleFiber i)
     change ((P') U).part _=_
     have hP:∀ i, Burns o i (S.mount t i) t:= (S.vessel t).clearBurn _ (S.wet _ hB') (S.turn _ hB');
     have ht: (P') U=Poly.pass (Mach (Names V J) q')*L'.reap (Q U) :=by
         rw [hz']; change _= Poly.pass _*L'.reap (play R _ S.river _ _)
         unfold play; rw [map_smul]; dsimp only; rw [S.yields _ U hB', pass_add (mute ..) (show _ from by rw [Poly.part_sum]; exact sum_eq_zero fun i _=> (hP i).sil _)]; rw [mul_assoc,mul_smul_comm]
     unfold g' k'; rw [if_neg hh,if_neg hh,ht,shock]; simp_rw [Poly.pass_part _ (mute ..), whisper _ _ (mute ..),Accent.sing,hw,one_mul,zero_mul,add_zero]; exact (hz.served.relay (J:=Names V J) (fun i=>(hz.foot i).1) hr U).1 i
   unfold g' k'; rw [if_neg hi,if_neg hi]; exact (hz.foot _).2
where
  default_perm (a:Equiv.Perm V): Fibers.Permutes (partialGroup V L) (nome a) (nome a):=⟨fun _=>rfl,fun _=>rfl⟩
end YM.MergeProof.Ribbons.ManyCopies
