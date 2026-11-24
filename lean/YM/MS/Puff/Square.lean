import YM.MS.Puff.Mint
/-!
Half the ordered bracket is exactly the stipulated picks operation on even marks. Need no
rank or limits, only where both factors commute under the bracket.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Function Finset
open Koszul Book Book.Convolve Rake
variable {E F W:Type}[LinearOrder W][AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F] {s:Finset W}
namespace Stencil
open SplitP
variable (X:Angled E) (f:Finset W→E) (hs:∀ i j,X ( f i ) ( f j )= X ( f j ) ( f i ))(hv:f ∅=0)
-- split subsets including own `s`. i=∅ term zero already.Simplify.
include hs hv
lemma halfB (s:Finset W) : ( (2:ℂ)⁻¹ ) • ( marked W ).Lift X f f s= ∑ i∈picks s,X ( f i ) (f ( s\i )):= by
   obtain h|h:= (em s.Nonempty); swap; · rw [Finset.not_nonempty_iff_eq_empty.mp h]; unfold Lift; simp [picks,marked,subs,hv] -- lint
   let p:= s.min' h; let L i:= X (f i) (f (s\ i)); let A:=s.powerset.filter (fun i=> p∈i); let B:=s.powerset.filter (fun i=> p∉i); have H : ∑ i∈ picks s,L i=∑ i∈B,L i:= by
       refine Finset.sum_subset ?_ ?_; · intro i hi; obtain ⟨hh,hx⟩:=Finset.mem_filter.mp hi; exact Finset.mem_filter.mpr ⟨ hh,( by simpa only [ h, ↓reduceDIte ] using hx.2 ) ⟩
       intro i hi hx; by_cases hp:i=∅; subst i; unfold L; rw [hv,map_zero]; rfl; exact False.elim ( hx ( Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hi |>.1, Finset.nonempty_iff_ne_empty.mpr hp, dif_pos h ▸ (Finset.mem_filter.mp hi).2⟩ ))
   have he: ∑ i∈B,L i=∑ i∈ A,L i:= by
       apply Finset.sum_bij' (fun i _=> s\ i) (fun i _=>s\ i) <;> intro i hi; all_goals simp only [A,B,Finset.mem_filter,Finset.mem_powerset] at *; all_goals obtain ⟨ha,hb⟩:=hi; try solve|grind|exact ⟨ sdiff_subset, mem_sdiff.mpr ⟨ min'_mem s h,hb ⟩ ⟩|exact ⟨ sdiff_subset,fun ht=> ht.2 hb ⟩
       unfold L; rw [show s \ (s \ i)=i from (by grind),hs]
   suffices hk:(marked W).Lift X f f s=(2:ℂ) • (∑ i∈B, L i) by rw [hk, ← H, inv_smul_smul₀ (by norm_num : (2:ℂ)≠0) ]
   rw [ SplitP.loan,show (marked W).pieces s=subs s from rfl,sumS (fun a b=>X (f a) (f b)) ]; -- syntactic issue.
   rw [ show (∑ i∈s.powerset,X (f i) (f (s\ i)))=_ from ( Finset.sum_filter_add_sum_filter_not s.powerset ( fun i=> p∈ i ) L ).symm ];
   rw [ ← he ]; exact (two_smul ℂ _).symm
end Stencil
end YM.MS.Puff
