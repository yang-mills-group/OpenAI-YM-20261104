import YM.OPE.Compatible.Bower.Blind
/-!
# Commitments for principal careers

Select finish time independently of physical layout when soloing a
witness at exactly the second wave. Then change it *after* finding
its linear report; it will continue to actual geometry frontier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Wave
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights
open scoped Topology BigOperators Classical
variable {X V I G' : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{v:X} {m:X→ℕ}
    (W:Type)[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype W][DecidableEq W]
    {G:Gauge}{C:Family G}{p n N b d:ℕ}{l:ℕ→ℕ}
-- selectors normal and postponed pivot under F extras
def columns (F:Finset X)(v:X) : brim D F ⊕ W → X:= Sum.elim (fun x=> x.val) (fun _=>v)
def brimEnd (F:Finset X)(s:X→ℕ)(i:ℕ): brim D F⊕ W→ℕ:= Sum.elim (fun x=>s x.val) fun _=>i
variable (P:Wave m F K n) (Q': Ensemble V) (E:Track C.path V p) (o:X→ Track C.path V p)
variable {j:X→ℕ}(h:CutOrder C Q' D U m j N p E o b l)(hp:F⊆U) (hf:∀ x:brim D F, n≤ roof U m N x.val)
set_option quotPrecheck false
local notation "F!" => columns D W F v -- check order
local notation "f'" => columns D W K v
local notation "p!" => riseUp W D P
local notation "N'" => finishAt D m
include h hf hp
omit [Fintype V][DecidableEq V] in
lemma aim_pledge (k:X→ℕ)(hn:d≤ n)(hx :∀ i:brim D F, k i.val ≤ n ∧ N' i.val ≤ k i.val)
    (hl:∀ i,d ≤ i→ i ≤ n→∀ x:V,x≠Q'.v→ o v i x=affine (Q'.move x).1 (E i x) (o v i Q'.v)) -- actual need echoes v beyond roof. pass explicit.
    (he:∀ i:brim D K,i.val∈F→k i.val=N' i.val)
    (hb:∀ i:brim D F, (topHat D P i).val∈F→ k i.val=N' i.val) : Bind C Q' E p! (o∘ F!) (o∘ f') n (brimEnd D W F k d) (brimEnd D W K k d) (brimEnd D W K j d):=by
    have ht(i:brim D K): i.val∈allUp D U:= brim_under D U K (P.next.trans hp) i.2
    have hk(i:brim D K)(hi:i.val∈F): m i.val=n:=taken D P i hi
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rintro (i|i); exact (hx i).1; exact hn
    · rintro (i|i) h
      · obtain ⟨a,ha,hh⟩:= take_left D P i h; refine ⟨_,ha,congr_arg k hh, congr_arg o hh⟩
      exact ⟨_,take_right D P i,rfl,rfl⟩
    · rintro (i|i) hQ
      · have hp':i.val∈F:= not_not.mp ((solos ..).not.mp hQ); change _< k i.val; rw [he _ hp']; exact lt_of_lt_of_le h.head (lower_earliest D U m h.plan _ (ht i))
      exact False.elim (hQ (pilots D P _))
    · rintro (i|i) hQ
      · have hp':i.val∈F:= not_not.mp ((solos ..).not.mp hQ); obtain ⟨hx',hz'⟩:= h.epochs i.val (hp hp'); exact ⟨(he i hp').trans_le hx',le_trans hz' (hk i hp').le⟩
      exact False.elim (hQ (pilots D P _))
    · rintro (i|i) hQ
      · have hp':i.val∈F:= not_not.mp ((solos ..).not.mp hQ); exact hk i hp' ▸ h.inHost i.val (hp hp')
      exact False.elim (hQ (pilots D P _))
    · rintro (i|i) hQ
      · intro t hs hu; refine h.pare i.val (ht i) _ ?_ (hu.trans_le (P.upward D hp N hf i)); exact (he i (not_not.mp ((solos ..).not.mp hQ))).symm ▸ hs
      exact False.elim (hQ (pilots D P _))
    · rintro (i|i) hQ
      · have hu:i.val∈F:=not_not.mp ((solos ..).not.mp hQ); exact ⟨fun m hi hz=>h.moves.mare _ (le_trans (lower_earliest D U _ h.plan _ (ht i)) ((he i hu).symm ▸ hi)) (lt_of_lt_of_le (lt_of_lt_of_le hz (hk i hu).ge) ((Series.high D h.plan (hp hu)).trans h.next.le))⟩
      exact False.elim (hQ (pilots D P _))
    · rintro (i|i) m hm H
      · refine h.echo i.val (ht i) _ ?_ (H.trans (P.upward D hp N hf i)); by_cases hv:i.val∈ F; exact (he i hv).symm ▸ hm; exact le_trans (hx ⟨i.val,P.sweep D i.2 hv⟩).2 hm
      exact hl m hm H
    rintro (i|i) hQ
    · have h : (topHat D P i).val∈ F:=not_not.mp (fun h=> hQ ((solos ..).mpr h)); exact (hb i h).trans (children D P i h)
    exact False.elim (hQ (pilots D P _))
end YM.OPE.Arboreal.Wave
