import YM.MergeProof.Garnish
import YM.MSbar.Fusion.Quark
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Rafts
variable {arn:ℕ}
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Entangle Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}{S:StepData c f}
variable {v:V}{P:V→Motion}{E:V→Site c}{B:V→Equiv.Perm V}
local notation "X"=> Aged arn V
variable {o:Name arn V→ Site f}{b:Name arn V→Site c}
    {L:Name arn V→ Config G f→ℂ}{K:Name arn V→ Res G f}{H:Name arn V→ Res G c}{a t:Fin (arn+1)→ℝ}{g:Name arn V→ℂ}
    {N:ℕ} {d e u x φ ψ c':ℝ}{w:Name arn V→ℝ}
    {Y: Config G f→Poly (Aged arn V)}
local notation "r"=> fun i=> S.ratio.embed (E i)
set_option quotPrecheck false
lemma pool (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o b L K H g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i))) (hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:Fin (arn+1),w (i,j)=w (v,j)) (hp:∀ i:Fin (arn+1), let y:Name arn V:=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (b y) 1 (L y) (K y) (H y) (g y) (a i) (t i) D) (hP:Occupancy o N)(hd:0 ≤ d)(he:u+1 ≤ R.p.supportExponent)(ha:∀ i:Name arn V,2*w i*a i.snd ≤ d)(hK:∀ i:Name arn V,w i*t i.snd ≤ x)(hY:e+1 ≤ A.p.supportExponent+2) :
    ∃ (I:Type) (_: Fintype I) (M:I→Hat (Aged arn V) R), Cohere v P (fun i=> S.ratio.embed (E i)) B π M ∧ Offer o M w R.p.B u (N*siteFactor R.p.B*d) ∧ ∃ ψ:Name arn V→Response G c, Garnish A.p b ψ w e x ∧ relates v P E ψ ∧ (∀ i U j,∑ l,owl (M l) D i j U=H i j U-hook A.activities A.p.threshold (ψ i) j U) ∧ (∀ U,∑ i,odour (M i) U=Mach (Aged arn V) (fun i=>L i U-g i)) ∧ ∀ j U,∑ i,fragrance (M i) U j=Mach (Aged arn V) (fun i=> K i j U):=by
    obtain ⟨I,hI,M,p,hM,hX,Ht⟩:=quay v P E B o b L K H a t g S hD hs hx π hw hy hp; let Z:= Σ j:Name arn V,I j.snd
    have hg(i:Z):=(hM i.1).ran i.2
    have hz:Rooted (fun i=>(M i).s.val) (fun i=> (M i).M.crest) R.p.B R.p.supportExponent (fun i=> Menu.fare (M i) w) d:=by
       intro i; refine ⟨fun x=>?_, Summable.of_finite,?_⟩
       · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (Crew _ hw); rfl
       rw [tsum_fintype,Fintype.sum_sigma,sum_eq_single i];
       · calc
            _ = ∑ v:I _, R.p.mass (M ⟨i,v⟩).M.crest (Menu.fare (M ⟨i,v⟩) w) := sum_congr rfl fun j _=> if_pos (show i∈(M ⟨i,j⟩).s.val from ((hM i).ran j).1.symm ▸ (show i∈((X).fire i).val from mem_singleton_self _))
            _ ≤ _ := (hM i).fare.trans (ha i)
       · intro j _ hj; apply Finset.sum_eq_zero; intro k _; exact if_neg fun hi=> hj (Finset.mem_singleton.mp (show i∈((X).fire j).val from ((hM j|>.ran k).1) ▸ (show i∈ (M ⟨j,k⟩).s.val from hi))|>.symm)
       simp
    have hG: Garnish A.p b p w e x:=by
       have hB i:=(hM i).bill
       refine ⟨fun i t=> (hB i).shaped _,fun i k=> (hB i).marked _,fun i=>?_⟩; obtain ⟨t,ht,hQ⟩:= (hB i).toll
       refine ⟨t,hQ,le_trans ?_ (hK i)⟩
       apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap ht univ) (hw i).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold reservedMass; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr)) (hQ j).1) (hw i).le
    refine ⟨Z,inferInstance,M,Ht, ⟨fun i=>?_,root_hit hP (fun _=>Crew _ hw) hd ?_ (hz.mono (fun _=>Crew _ hw) (fun _=>le_rfl) he le_rfl)⟩,p,hG,hX,fun i U j=>?_,fun U=>?_,fun j U=>?_⟩
    · rw [(hg i).1]; change Finset.image _ {_}⊆_; simp only [image_singleton,singleton_subset_iff]; exact (hg _).2
    · intro i hi; exact ⟨i.1,(hg i).1.symm ▸ (show i.1∈((X).fire i.1).val from mem_singleton_self _),(hg i).2⟩
    · rw [Fintype.sum_sigma,sum_eq_single i]; exact hM i|>.tells j U
      · intro k _ hk; refine sum_eq_zero (fun l _=>?_); unfold owl; split
        next ht=> exact False.elim (hk (((X).fire_inj k i).mp (((hM k).ran l).1.symm.trans ht)))
        next hh=> rfl -- parser
      simp
    · rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> (hM i).note U
    rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> (hM i).verse j U
-- stronger Serves

def Serves (R:Rep G f)(L:Name arn V→ Config G f→ℂ)(K:Name arn V→ Res G f)(Y:Config G f→Poly (Aged arn V))(v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(o:Name arn V→Site f)(w:Name arn V→ℝ)(t d:ℝ):Prop:=∃ F Z, Carton o F Z R.p.threshold ∧ Towed w id F R.p.B t d ∧ Towed w Prod.fst Z R.p.B t d ∧ Horn v P E B F Z ∧ Y= restore R L K F Z
end YM.MergeProof.Rafts
